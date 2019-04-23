#lang racket

;; This is a redex model of the semantics of webassembly from the paper
;;   "Bringing the Web up to Speed with WebAssembly"
;;   Haas et al.

(require redex
         pict
         pict/snip)

;; wasm defines memory for module instances in 64Ki increments, but this is
;; unwieldly in redex so we define the increment in bytes here
(define *page-size* 20)

;; some non-terminals (like for modules) differ from the paper due to redex
;; constraints on non-terminals appearing as keywords, and some forms have
;; extra keywords for ease of identification
(define-language wasm-lang
  ;; types
  (t   ::= t-i t-f)
  (t-f ::= f32 f64)
  (t-i ::= i32 i64)
  (tp  ::= i8 i16 i32)
  (sx  ::= sx-s sx-u) ; renamed to avoid conflict with s non-terminal
  (tf  ::= (-> (t ...) (t ...)))
  (tg  ::= t (mut t))

  ;; instructions
  (e-no-v ::= unreachable
              nop
              drop
              select
              (block tf e*)
              (loop tf e*)
              (if tf e* else e*)
              (br i)
              (br-if i)
              (br-table i i ...)
              return
              (call i)
              (call-indirect tf)
              (get-local i)
              (set-local i)
              (tee-local i)
              (get-global i)
              (set-global i)
              (load t a o)
              (load t tp sx a o)
              (store t a o)
              (store t tp a o)
              current-memory
              grow-memory
              ;; prim ops become a little verbose due to type constraints
              (unop-i t-i)
              (unop-f t-f)
              (binop-i t-i)
              (binop-f t-f)
              (testop-i t-i)
              (relop-i t-i)
              (relop-f t-f)
              (cvtop t t)
              (cvtop t t sx))
  (e    ::= e-no-v
            (const t c))

  ;; primitive operations
  [unop     ::= unop-i unop-f]
  (unop-i   ::= clz ctz popcnt)
  (unop-f   ::= neg abs ceil floor trunc nearest sqrt)
  [binop    ::= binop-i binop-f]
  (binop-i  ::= add sub mul div-s div-u rem-s rem-u and
                or xor shl shr-s shr-u rotl rotr)
  (binop-f  ::= add sub mul div min max copysign)
  (testop   ::= testop-i)
  (testop-i ::= eqz)
  (relop    ::= relop-i relop-f)
  (relop-i  ::= eq ne lt-u lt-s gt-u gt-s le-u le-s ge-u ge-s)
  (relop-f  ::= eq ne lt gt le ge)
  (cvtop    ::= convert reinterpret)

  ;; sequences of expressions
  ;; (we use this to avoid splicing)
  (e*   ::= ϵ
            (e e*))

  (c    ::= number)

  ;; constant numerals
  ((i j l k m n a o) integer)

  ;; bytes
  (b    ::= integer)

  ;; modules & functions
  (f      ::= (func (ex ...) tf local (t ...) e*)
              (func (ex ...) tf im))
  (m-glob ::= (global (ex ...) tg e ...)
              (global (ex ...) tg im))
  (m-tab  ::= (table (ex ...) n i ...)
              (table (ex ...) n im))
  (m-mem  ::= (memory (ex ...) n)
              (memory (ex ...) n im))
  (im     ::= (import string string))
  (ex     ::= (export string))
  (mod    ::= (module f ... m-glob ...)
              (module f ... m-glob ... m-tab)
              (module f ... m-glob ... m-mem)
              (module f ... m-glob ... m-tab m-mem)))

(define-extended-language wasm-runtime-lang wasm-lang
  ;; administrative expressions
  (e-no-v  ::= ....
               trap
               (call cl)
               (label n {e*} e*)
               (local n {i (v ...)} e*))

  ;; runtime
  (s       ::= {(inst modinst ...) (tab tabinst ...) (mem meminst ...)})
  (modinst ::= {(func cl ...) (glob v ...)}
               {(func cl ...) (glob v ...) (tab i)}
               {(func cl ...) (glob v ...) (mem i)}
               {(func cl ...) (glob v ...) (tab i) (mem i)})
  (tabinst ::= (cl ...))
  (meminst ::= (b ...))
  (cl      ::= {(inst i) (code f)})

  (F       ::= (v ...))
  ;; this is needed for the actual spec
  #;
  (F       ::= {(locals v ...) (module modinst)})

  (v       ::= (const t c))
  (v*      ::= ϵ
               (v v*))

  ;; evaluation contexts
  ;; using an inductive definition instead of using sequences because
  ;; we would need splicing holes otherwise
  (E       ::= hole
               (v E)
               ((label n (e*) E) e*)))

;; helper for constructing instruction sequences
(define-metafunction wasm-runtime-lang
  seq : e ... -> e*
  [(seq) ϵ]
  [(seq e_0 e_1 ...)
   (e_0 (seq e_1 ...))])

(define-metafunction wasm-runtime-lang
  seq* : e ... e* -> e*
  [(seq* e*) e*]
  [(seq* e_0 e_1 ... e*_2)
   (e_0 (seq* e_1 ... e*_2))])

;; append two e* expression lists
(define-metafunction wasm-runtime-lang
  e*-append : e* e* -> e*
  [(e*-append ϵ e*) e*]
  [(e*-append (e_0 e*_0) e*_1)
   (e_0 (e*-append e*_0 e*_1))])

(module+ test
  (test-equal (term (e*-append ϵ (drop ϵ)))
              (term (drop ϵ)))
  (test-equal (term (e*-append ((const i32 0) ϵ) (drop ϵ)))
              (term ((const i32 0) (drop ϵ)))))

;; find the nesting depth of values around the hole in the eval context
(define-metafunction wasm-runtime-lang
  v-depth : E -> number
  [(v-depth hole) 0]
  [(v-depth (in-hole E (v hole)))
   ,(add1 (term (v-depth E)))]
  [(v-depth (in-hole E ((label n {e*_0} hole) e*_1)))
   0])

(module+ test
  (test-equal (term (v-depth hole)) (term 0))
  (test-equal (term (v-depth ((const i32 2) ((const i32 1) hole))))
              (term 2))
  (test-equal (term (v-depth ((label 1 {ϵ} ((const i32 1) hole)) ϵ)))
              (term 1))
  (test-equal (term (v-depth ((const i32 2) ((label 1 {ϵ} ((const i32 1) hole)) ϵ))))
              (term 1)))

;; split an eval context into two contexts:
;;   - an outer context surrounding the second
;;   - an inner context with nested values around a hole
;; precondition: E actually has l-nested values when called
(define-metafunction wasm-runtime-lang
  v-split : E number -> (E E)
  [(v-split hole l)
   (hole hole)]
  [(v-split (in-hole E (v hole)) 0)
   ((in-hole E_outer (v hole)) hole)
   (where (E_outer hole) (v-split E 0))]
  [(v-split (in-hole E (v hole)) l)
   (E_outer (in-hole E_v (v hole)))
   (where (E_outer E_v) (v-split E ,(sub1 (term l))))]
  [(v-split (in-hole E ((label n {e*_0} hole) e*_2)) 0)
   ((in-hole E_outer ((label n {e*_0} hole) e*_2))
    hole)
   (where (E_outer hole) (v-split E 0))])

(module+ test
  (test-equal (term (v-split hole 0))
              (term (hole hole)))
  (test-equal (term (v-split ((const i32 2) ((const i32 1) hole)) 1))
              (term (((const i32 2) hole)
                     ((const i32 1) hole))))
  (test-equal (term (v-split ((label 1 {ϵ} ((const i32 0) ((const i32 1) hole))) ϵ) 1))
              (term (((label 1 {ϵ} ((const i32 0) hole)) ϵ)
                     ((const i32 1) hole)))))

;; find the depth of label nestings in E
(define-metafunction wasm-runtime-lang
  label-depth : E -> number
  [(label-depth hole)  0]
  [(label-depth (v E)) (label-depth E)]
  [(label-depth ((label n {e*_0} E) e*_1))
   ,(add1 (term (label-depth E)))])

(module+ test
  (test-equal (term (label-depth hole)) 0)
  (test-equal (term (label-depth ((const i32 2) ((const i32 1) hole))))
              0)
  (test-equal (term (label-depth ((label 1 {ϵ} ((const i32 0) ((const i32 1) hole))) ϵ)))
              1)
  (test-equal (term (label-depth ((label 1 {ϵ} ((const i32 0) ((const i32 1) ((label 1 {ϵ} hole) ϵ)))) ϵ)))
              2))

;; extract a closure out of the func part of store
(define-metafunction wasm-runtime-lang
  store-func : s i j -> cl
  [(store-func {(inst modinst_0 ... modinst modinst_1 ...) any_0 ...} i j)
   cl
   (side-condition (= (length (term (modinst_0 ...))) (term i)))
   (where {(func cl_0 ... cl cl_1 ...) any_1 ...} modinst)
   (side-condition (= (length (term (cl_0 ...))) (term j)))])

(module+ test
  (let ()
    (define f1 (term (func () (-> () ()) local () (seq nop))))
    (define modinst1 (term {(func {(inst 0) (code ,f1)}) (glob)}))
    (test-equal (term (store-func {(inst ,modinst1) (tab) (mem)} 0 0))
                (term {(inst 0) (code ,f1)}))))

;; extract a closure from the tab part of store
(define-metafunction wasm-runtime-lang
  store-tab : s i j -> cl
  [(store-tab {(inst modinst_0 ... modinst modinst_1 ...)
               (tab tabinst_0 ... tabinst tabinst_1 ...)
               any_0 ...}
              i j)
   cl
   (side-condition (= (length (term (modinst_0 ...))) (term i)))
   (where {any_1 ... (tab i_tab) any_2 ...} modinst)
   (side-condition (= (length (term (tabinst_0 ...))) (term i_tab)))
   (where (cl_0 ... cl cl_1 ...) tabinst)
   (side-condition (= (length (term (cl_0 ...))) (term j)))])

;; read a global value
(define-metafunction wasm-runtime-lang
  store-glob : s i j -> v
  [(store-glob {(inst modinst_0 ... modinst modinst_1 ...) any_0 ...} i j)
   v
   (side-condition (= (length (term (modinst_0 ...))) (term i)))
   (where {any_f (glob v_0 ... v v_1 ...) any_1 ...} modinst)
   (side-condition (= (length (term (v_0 ...))) (term j)))])

;; write a global value
(define-metafunction wasm-runtime-lang
  store-glob= : s i j v -> s
  [(store-glob= {(inst modinst_0 ... modinst modinst_1 ...) any_0 ...} i j v_new)
   {(inst modinst_0 ... modinst_new modinst_1 ...) any_0 ...}
   (side-condition (= (length (term (modinst_0 ...))) (term i)))
   (where {any_f (glob v_0 ... v v_1 ...) any_1 ...} modinst)
   (side-condition (= (length (term (v_0 ...))) (term j)))
   (where modinst_new {any_f (glob v_0 ... v_new v_1 ...) any_1 ...})])

;; read from memory
(define-metafunction wasm-runtime-lang
  store-mem : s i j n -> (b ...) or #false
  [(store-mem {(inst modinst_0 ... modinst modinst_1 ...)
               any_1
               (mem meminst_0 ... meminst meminst_1 ...)}
              i j n)
   (b ...)
   (side-condition (= (length (term (modinst_0 ...))) (term i)))
   (where {any_i ... (mem i_mem)} modinst)
   (side-condition (= (length (term (meminst_0 ...))) (term i_mem)))
   (where (b_0 ... b_rest ...) meminst)
   (side-condition (= (length (term (b_0 ...))) (term j)))
   (where (b ... b_end ...) (b_rest ...))
   (side-condition (= (length (term (b ...))) (term n)))]
  [(store-mem any ...)
   #false])

(define-metafunction wasm-runtime-lang
  sizeof : any -> n
  [(sizeof i8)  1]
  [(sizeof i16) 2]
  [(sizeof i32) 4]
  [(sizeof i64) 8]
  [(sizeof f32) 4]
  [(sizeof f64) 8])

(define-metafunction wasm-runtime-lang
  const-reinterpret-packed : t (b ...) sx -> c
  [(const-reinterpret-packed t (b ...) sx-s)
   ,(integer-bytes->integer (list->bytes (term (b ...))) #t)]
  [(const-reinterpret-packed t (b ...) sx-u)
   ,(integer-bytes->integer (list->bytes (term (b ...))) #f)])

(define-metafunction wasm-runtime-lang
  const-reinterpret : t (b ...) -> c
  [(const-reinterpret t-i (b ...))
   ,(integer-bytes->integer (list->bytes (term (b ...))) #t)]
  [(const-reinterpret t-f (b ...))
   ,(floating-point-bytes->real (list->bytes (term (b ...))))])

(define-metafunction wasm-runtime-lang
  bits : n t c -> (b ...)
  [(bits n i32 i)
   ,(take (bytes->list (integer->integer-bytes (term i) 4 #t)) (term n))]
  [(bits n i64 i)
   ,(take (bytes->list (integer->integer-bytes (term i) 8 #t)) (term n))]
  [(bits n f32 float)
   ,(take (bytes->list (real->floating-point-bytes (term float) 4)) (term n))]
  [(bits n f64 float)
   ,(take (bytes->list (real->floating-point-bytes (term float) 8)) (term n))])

(define-metafunction wasm-runtime-lang
  store-mem= : s i j n (b ...) -> s or #false
  [(store-mem= {(name any_0 (inst modinst_0 ... modinst modinst_1 ...))
                any_1
                (mem meminst_0 ... meminst meminst_1 ...)}
               i j n (b_new ...))
   {any_0 any_1 (mem meminst_0 ... meminst_new meminst_1 ...)}
   (side-condition (= (length (term (modinst_0 ...))) (term i)))
   (where {any_i ... (mem i_mem)} modinst)
   (side-condition (= (length (term (meminst_0 ...))) (term i_mem)))
   (where (b_0 ... b_rest ...) meminst)
   (side-condition (= (length (term (b_0 ...))) (term j)))
   (where (b ... b_end ...) (b_rest ...))
   (side-condition (= (length (term (b ...))) (term n)))
   (where meminst_new (b_0 ... b_new ... b_end ...))]
  [(store-mem= any ...) #false])

;; metafunctions for manipulating memory size
(define-metafunction wasm-runtime-lang
  memory-size : s i -> n
  [(memory-size {(name any_0 (inst modinst_0 ... modinst modinst_1 ...))
                 any_1
                 (mem meminst_0 ... meminst meminst_1 ...)}
                i)
   n_size
   (side-condition (= (length (term (modinst_0 ...))) (term i)))
   (where {any_i ... (mem i_mem)} modinst)
   (side-condition (= (length (term (meminst_0 ...))) (term i_mem)))
   (where n_size ,(/ (length (term meminst)) *page-size*))])

(define-metafunction wasm-runtime-lang
  expand-memory : s i k -> (s n)
  [(expand-memory {(name any_0 (inst modinst_0 ... modinst modinst_1 ...))
                   any_1
                   (mem meminst_0 ... meminst meminst_1 ...)}
                  i k)
   (s_new n_size)
   (side-condition (= (length (term (modinst_0 ...))) (term i)))
   (where {any_i ... (mem i_mem)} modinst)
   (side-condition (= (length (term (meminst_0 ...))) (term i_mem)))
   (where meminst_new ,(append (term meminst)
                               (flatten (make-list (term k) (make-list *page-size* 0)))))
   (where n_size ,(/ (length (term meminst_new)) *page-size*))
   (where s_new {any_0 any_1 (mem meminst_0 ... meminst_new meminst_1 ...)})])

;; extract the code from a closure
(define-metafunction wasm-runtime-lang
  cl-code : cl -> f
  [(cl-code {any (code f)}) f])

;; extract the instance index from a closure
(define-metafunction wasm-runtime-lang
  cl-inst : cl -> i
  [(cl-inst {(inst i) any}) i])

;; append two Fs together
(define-metafunction wasm-runtime-lang
  F-append : F F -> F
  [(F-append () F) F]
  [(F-append (v_1 ... v) (v_2 ...))
   (F-append (v_1 ...) (v v_2 ...))])

;; convert a nested v* to a (v ...), uses accumulator
(define-metafunction wasm-runtime-lang
  v*->F : v* -> F
  [(v*->F v*) (v*->F-helper v* ())])

(define-metafunction wasm-runtime-lang
  v*->F-helper : v* F -> F
  [(v*->F-helper ϵ F) F]
  [(v*->F-helper (v v*) (v_acc ...))
   (v*->F-helper v* (v_acc ... v))])

;; implement primitives
(define-metafunction wasm-runtime-lang
  do-unop : unop t c -> c
  ;; TODO: integer ops
  [(do-unop neg t-f c) ,(- (term c))]
  [(do-unop abs t-f c) ,(abs (term c))]
  [(do-unop ceil t-f c) ,(ceiling (term c))]
  [(do-unop floor t-f c) ,(floor (term c))]
  [(do-unop trunc t-f c) ,(truncate (term c))]
  [(do-unop nearest t-f c) ,(round (term c))]
  [(do-unop sqrt t-f c) ,(sqrt (term c))])

(define-metafunction wasm-runtime-lang
  do-binop : binop t c c -> c
  ;; TODO: should handle overflow and such more properly
  [(do-binop add t c_1 c_2) ,(+ (term c_1) (term c_2))]
  [(do-binop sub t c_1 c_2) ,(- (term c_1) (term c_2))]
  [(do-binop mul t c_1 c_2) ,(* (term c_1) (term c_2))]
  [(do-binop and t-i c_1 c_2) ,(bitwise-and (term c_1) (term c_2))]
  [(do-binop or t-i c_1 c_2) ,(bitwise-ior (term c_1) (term c_2))]
  ;; TODO: more ops
  )

(define-metafunction wasm-runtime-lang
  do-testop : testop t c -> c
  [(do-testop eqz t-i 0) 1]
  [(do-testop eqz t-i c) 0])

(define-metafunction wasm-runtime-lang
  do-relop : relop t c c -> c
  ;; TODO: integer ops
  [(do-relop eq t c_1 c_2) ,(if (= (term c_1) (term c_2)) 1 0)]
  [(do-relop ne t c_1 c_2) ,(if (= (term c_1) (term c_2)) 0 1)])

;; helpers for pretty printing / drawing as stack picts
(define (pp/pict state port width text)
  (redex-let
   wasm-runtime-lang
   ([{s F e* i} state])
   (define p (term->pict (term e*)))
   (send text insert (new pict-snip% [pict p]))))

(define (stack-pict str)
  (cc-superimpose
   (filled-rectangle 100 50
                     #:color "white"
                     #:border-color "black")
   (text str)))

(define (indent pict)
  (hc-append (blank 30 1) pict))

(define term->pict
  (term-match/single
   wasm-runtime-lang
   [((const t c) e*)
    (let ()
      (define str (format "(~a.const ~a)" (term t) (term c)))
      (vc-append (stack-pict str)
                 (term->pict (term e*))))]
   [((call cl) e*)
    (let ()
      (vc-append (stack-pict "(call #<closure>)")
                 (term->pict (term e*))))]
   [((label n {e*_0} e*_1) e*_2)
    (let ()
      (vc-append (stack-pict (~a "label " (term n)))
                 (indent (term->pict (term e*_1)))
                 (term->pict (term e*_2))))]
   [((local n {i F} e*_1) e*_2)
    (let ()
      (vc-append (stack-pict (format "local ~a ~a" (term n) (term i)))
                 (indent (term->pict (term e*_1)))
                 (term->pict (term e*_2))))]
   [((block tf e*_1) e*_2)
    (let ()
      (vc-append (stack-pict (format "block ~a" (term tf)))
                 (indent (term->pict (term e*_1)))
                 (term->pict (term e*_2))))]
   [((loop tf e*_1) e*_2)
    (let ()
      (vc-append (stack-pict (format "loop ~a" (term tf)))
                 (indent (term->pict (term e*_1)))
                 (term->pict (term e*_2))))]
   [((if tf e*_0 else e*_1) e*_2)
    (let ()
      (vc-append (stack-pict (format "if ~a" (term tf)))
                 (indent (term->pict (term e*_0)))
                 (stack-pict (format "then"))
                 (indent (term->pict (term e*_1)))
                 (term->pict (term e*_2))))]
   [(e e*)
    (vc-append (stack-pict (format "~a" (term e)))
               (term->pict (term e*)))]
   [ϵ (blank 0 0)]))

(define-syntax-rule (wasm-pp-traces t)
  (traces wasm-> #:pp pp/pict t))

;; the actual reduction relation starts here
(define wasm->
  (reduction-relation
   wasm-runtime-lang
   #:domain (s F e* i)

   (--> (s F (trap (e e*)) i)
        (s F (trap ϵ) i)
        trap)
   (--> (s F (in-hole E (trap e*)) i)
        (s F (trap ϵ) i)
        (side-condition (not (redex-match wasm-runtime-lang hole (term E))))
        trap-context)

   (==> ((const t c) ((unop t) e*))
        ((const t (do-unop unop t c)) e*)
        unop)

   (==> ((const t c_1) ((const t c_2) ((binop t) e*)))
        ((const t c) e*)
        (where c (do-binop binop t c_1 c_2))
        binop)
   (==> ((const t c_1) ((const t c_2) ((binop t) e*)))
        (trap e*)
        binop-trap)

   (==> ((const t c) ((testop t) e*))
        ((const i32 (do-testop testop t c)) e*)
        testop)

   (==> ((const t c_1) ((const t c_2) ((relop t) e*)))
        ((const i32 (do-relop relop t c_1 c_2)) e*)
        relop)

   ;; TODO: convert

   (==> ((const t_1 c) ((reinterpret t_2 t_1) e*))
        ((const t_2 (const-reinterpret t_2 (bits (sizeof t_1) t_1 c))) e*)
        reinterpret)

   ;; generally these rules need to mention the "continuation" in the sequence
   ;; of instructions because Redex does not allow splicing holes with a
   ;; sequence of s-exps
   (==> (unreachable e*) (trap e*))
   (==> (nop e*) e*)
   (==> (v (drop e*)) e*)

   (==> (v_1 (v_2 ((const i32 0) (select e*))))
        (v_2 e*)
        select-false)
   (==> (v_1 (v_2 ((const i32 k) (select e*))))
        (v_1 e*)
        (side-condition (>= (term k) 1))
        select-true)

   ;; Redex can't express a pattern like n-level nestings of an
   ;; expression, so we explicitly compute the nesting depth of
   ;; values around the hole in the context E instead
   (++> (in-hole E ((block (-> (t_1 ...) (t_2 ...)) e*_0) e*_1))
        (in-hole E_outer (seq* (label k {ϵ} (in-hole E_v e*_0)) e*_1))

        (where l             ,(length (term (t_2 ...))))
        (where k             ,(length (term (t_1 ...))))
        (where (E_outer E_v) (v-split E k))
        block)

   (++> (in-hole E ((name e_loop (loop (-> (t_1 ...) (t_2 ...)) e*_0)) e*_1))
        (in-hole E_outer (seq* e_lbl e*_1))

        (where l             ,(length (term (t_2 ...))))
        (where k             ,(length (term (t_1 ...))))
        (where (E_outer E_v) (v-split E k))
        (where e_lbl         (label l {(seq e_loop)} (in-hole E_v e*_0)))
        loop)

   (==> ((const i32 0) ((if tf e*_1 else e*_2) e*))
        (seq* (block tf e*_2) e*)
        if-false)
   (==> ((const i32 k) ((if tf e*_1 else e*_2) e*))
        (seq* (block tf e*_1) e*)
        (side-condition (>= (term k) 1))
        if-true)

   (==> ((label n {e*_0} v*) e*_1)
        (e*-append v* e*_1)
        label-value)
   (==> ((label n {e*_0} trap) e*_1)
        (trap e*_1)
        label-trap)
   (==> ((label n {e*_0} (in-hole E ((br j) e*_1))) e*_2)
        (e*-append (in-hole E_v e*_0) e*_2)
        (where j (label-depth E))
        (where (E_outer E_v) (v-split E n))
        label-br)

   (==> ((const i32 0) ((br-if j) e*))
        e*
        br-if-false)
   (==> ((const i32 k) ((br-if j) e*))
        (seq (br j) e*)
        (side-condition (>= (term k) 1))
        br-if-true)

   (==> ((const i32 k) ((br-table i_1 ... i i_2 ...) e*))
        (seq* (br i) e*)
        (side-condition (= (length (term (i_1 ...))) (term k)))
        br-table-index)
   (==> ((const i32 k) ((br-table i_1 ... i) e*))
        (seq* (br i) e*)
        (side-condition (>= (term k) (length (term (i_1 ...)))))
        br-table-end)

   (--> (s F (in-hole E ((call j) e*)) i)
        (s F (in-hole E ((call (store-func s i j)) e*)) i)
        call-index)

   (--> (s F (in-hole E ((const i32 j) ((call-indirect tf) e*))) i)
        (s F (in-hole E ((call cl) e*)) i)
        (where cl (store-tab s i j))
        (where (func tf local (t ...) e*) (cl-code cl))
        call-indirect)

   ;; implicit side-condition: pattern match from previous case failed
   #;
   (--> (s F (in-hole E ((const i32 j) ((call-indirect tf) e*))) i)
        (s F (in-hole E (trap e*)) i)
        call-indirect-trap)

   (++> (in-hole E ((call cl) e*_0))
        (in-hole E_outer ((local m {(cl-inst cl) F} e*_block) e*_0))
        (where (func () (-> (t_1 ...) (t_2 ...)) local (t ...) e*_code) (cl-code cl))
        (where n ,(length (term (t_1 ...))))
        (where m ,(length (term (t_2 ...))))
        (where (E_outer E_v) (v-split E n))
        (where F (F-append (v*->F (in-hole E_v ϵ)) ((const t 0) ...)))
        (where e*_block (seq (block (-> () (t_2 ...)) e*_code)))
        call-closure)

   (==> ((local n {i F} v*) e*)
        (e*-append v* e*)
        local-value)

   (==> ((local n {i F} (trap e*_0)) e*_1)
        (trap ϵ)
        local-trap)

   (==> ((local n {i F} (in-hole E (return e*_0))) e*_1)
        (in-hole E_v e*_1)
        (where (E_outer E_v) (v-split E n))
        local-return)

   ;; specifies how to reduce inside a local/frame instruction via a
   ;; recursive use of the reduction relation
   (--> (s_0 F_0 (in-hole E ((local n {i F_1} e*_0) e*_2)) j)
        (s_1 F_0 (in-hole E ((local n {i F_2} e*_1) e*_2)) j)
        ;; apply --> recursively
        (where any_rec ,(apply-reduction-relation wasm-> (term (s_0 F_1 e*_0 i))))
        ;; only apply this rule if this reduction was valid
        (side-condition (not (null? (term any_rec))))
        ;; the relation should be deterministic, so just take the first
        (where (s_1 F_2 e*_1 i) ,(first (term any_rec)))
        frame-reduction)

   ;; reductions for operating on locals in frames
   (--> (s (name F (v_1 ... v v_2 ...)) (in-hole E ((get-local j) e*)) i)
        (s F (in-hole E (v e*)) i)
        (side-condition (= (length (term (v_1 ...))) (term j)))
        get-local)

   (--> (s (v_1 ... v v_2 ...) (in-hole E (v_new ((set-local j) e*))) i)
        (s (v_1 ... v_new v_2 ...) (in-hole E e*) i)
        (side-condition (= (length (term (v_1 ...))) (term j)))
        set-local)

   (==> (v ((tee-local j) e*))
        (v (v ((set-local j) e*)))
        tee-local)

   ;; reductions for operating on global store data
   (--> (s F (in-hole E ((get-global j) e*)) i)
        (s F (in-hole E ((store-glob s i j) e*)) i)
        get-global)

   (--> (s F (in-hole E (v ((set-global j) e*))) i)
        (s_new F (in-hole E e*) i)
        (where s_new (store-glob= s i j v))
        set-global)

   ;; reductions for operating on memory
   (--> (s F (in-hole E ((const i32 k) ((load t a o) e*))) i)
        (s F (in-hole E ((const t (const-reinterpret t (b ...))) e*)) i)
        (where (b ...) (store-mem s i ,(+ (term k) (term o)) (sizeof t)))
        load)

   (--> (s F (in-hole E ((const i32 k) ((load t tp sx a o) e*))) i)
        (s F (in-hole E ((const t (const-reinterpret-packed t (b ...) sx)) e*)) i)
        (where (b ...) (store-mem s i ,(+ (term k) (term o)) (sizeof tp)))
        load-packed)

   (--> (s F (in-hole E ((const i32 k) ((load t a o) e*))) i)
        (s F (in-hole E (trap e*)) i)
        (where #false (store-mem s i ,(+ (term k) (term o)) (sizeof t)))
        load-trap)

   (--> (s F (in-hole E ((const i32 k) ((load t tp sx a o) e*))) i)
        (s F (in-hole E (trap e*)) i)
        (where #false (store-mem s i ,(+ (term k) (term o)) (sizeof tp)))
        load-trap-packed)

   (--> (s F (in-hole E ((const i32 k) ((const t c) ((store t a o) e*)))) i)
        (s_new F (in-hole E e*) i)
        (where n (sizeof t))
        (where s_new (store-mem= s i ,(+ (term k) (term o)) n (bits n t c)))
        store)

   (--> (s F (in-hole E ((const i32 k) ((const t c) ((store t tp a o) e*)))) i)
        (s_new F (in-hole E e*) i)
        (where n (sizeof tp))
        (where s_new (store-mem= s i ,(+ (term k) (term o)) n (bits n t c)))
        store-packed)

   (--> (s F (in-hole E ((const i32 k) ((const t c) ((store t tp ... a o) e*)))) i)
        (s F (in-hole E (trap e*)) i)
        (where n (sizeof t))
        (where #false (store-mem= s i ,(+ (term k) (term o)) n (bits n t c)))
        store-trap)

   (--> (s F (in-hole E ((const i32 k) ((const t c) ((store t tp a o) e*)))) i)
        (s F (in-hole E (trap e*)) i)
        (where n (sizeof tp))
        (where #false (store-mem= s i ,(+ (term k) (term o)) n (bits n t c)))
        store-trap-packed)

   (--> (s F (in-hole E (current-memory e*)) i)
        (s F (in-hole E ((const i32 (memory-size s i)) e*)) i)
        current-memory)

   (--> (s F (in-hole E ((const i32 k) (grow-memory e*))) i)
        (s_new F (in-hole E ((const i32 j_newsize) e*)) i)
        (where (s_new j_newsize) (expand-memory s i k))
        grow-memory)

   ;; failure case for grow-memory omitted, alternatively we could institute a cap
   ;; and return -1 for that cap in the model

   with
   [(--> (s F (in-hole E x) i)
         (s F (in-hole E y) i))
    (==> x y)]
   [(--> (s F x i)
         (s F y i))
    (++> x y)]))

(module+ test
  (require rackunit)

  (define (wasm-eval a-term)
    (define results (apply-reduction-relation* wasm-> a-term))
    (unless (= (length results) 1)
      (error "wasm-> had non-deterministic evaluation or no result"))
    (define result (first results))
    (define result->eval-result
      (term-match/single
       wasm-runtime-lang
       [{s F (v ϵ) i} (term v)]
       [{s F (trap ϵ) i} (term trap)]))
    (result->eval-result (first results)))

  (define-syntax-rule (test-wasm--> x y)
    (test--> wasm-> x y))
  (define-syntax-rule (test-wasm-->> x y)
    (test-->> wasm-> x y))

  ;; for testing with side effects
  (define-syntax-rule (test-wasm-eval x y)
    (test-equal (wasm-eval x) y))

  ;; test helpers and terms
  (define default-memory
    (make-list *page-size* 0))
  (define mt-s (term {(inst) (tab) (mem)}))
  (define-syntax-rule (simple-config e*)
    (term (,mt-s () e* 0)))

  ;; sanity checks for the grammar
  (check-not-false
   (redex-match wasm-runtime-lang s mt-s))
  (check-not-false
   (redex-match wasm-runtime-lang F (second (simple-config ϵ))))
  (check-not-false
   (redex-match wasm-runtime-lang v (term (const i32 42))))
  (check-not-false
   (redex-match wasm-runtime-lang
                (in-hole E (v (drop e*)))
                (term ((const i32 42) (drop ϵ)))))

  ;; test primitives
  (test-wasm--> (simple-config (seq (const f32 42.0) (neg f32)))
                (simple-config (seq (const f32 -42.0))))
  (test-wasm--> (simple-config (seq (const i32 42) (eqz i32)))
                (simple-config (seq (const i32 0))))
  (test-wasm--> (simple-config (seq (const i32 42) (const i32 42) (ne i32)))
                (simple-config (seq (const i32 0))))

  ;; test drop & select
  (test-wasm--> (simple-config (seq (const i32 42) drop))
                (simple-config (seq)))
  (test-wasm--> (simple-config (seq (const i32 1) (const i32 2) (const i32 0) select))
                (simple-config (seq (const i32 2))))
  (test-wasm--> (simple-config (seq (const i32 1) (const i32 2) (const i32 42) select))
                (simple-config (seq (const i32 1))))

  ;; test labels
  (test-wasm--> (simple-config
                 (seq (label 1 {ϵ} ((const i32 2) ϵ))))
                (simple-config
                 (seq (const i32 2))))
  (test-wasm--> (simple-config
                 (seq (const i32 1) (label 1 {ϵ} ((const i32 2) ϵ))))
                (simple-config
                 (seq (const i32 1) (const i32 2))))
  (test-wasm--> (simple-config
                 (seq (label 1 {(drop ϵ)} (seq (label 1 {ϵ} (seq (const i32 1) (br 1)))))))
                (simple-config
                 (seq (const i32 1) drop)))

  ;; test block & related constructs
  (test-wasm--> (simple-config
                 (seq (const i32 1) (const i32 2) (block (-> (i32) (i32)) ϵ)))
                (simple-config
                 (seq (const i32 1) (label 1 {ϵ} ((const i32 2) ϵ)))))
  (test-wasm-->> (simple-config (seq (const i32 1) (const i32 2) (block (-> (i32) (i32)) ϵ)))
                 (simple-config (seq (const i32 1) (const i32 2))))
  (test-wasm-->> (simple-config (seq (const i32 1) (block (-> (i32) (i32)) (seq drop))))
                 (simple-config (seq)))

  ;; test branches
  (test-wasm--> (simple-config
                 (seq (const i32 1) (br-table 0 1 2)))
                (simple-config (seq (br 1))))
  (test-wasm--> (simple-config
                 (seq (const i32 2) (br-table 0 1 2)))
                (simple-config (seq (br 2))))
  (test-wasm--> (simple-config
                 (seq (const i32 3) (br-table 0 1 2)))
                (simple-config (seq (br 2))))

  ;; test frames / function calls / access to locals
  (test-wasm--> (simple-config
                 (seq (local 1 {1 ((const i32 1) (const i32 2) (const i32 3))}
                        (seq (get-local 1)))))
                (simple-config
                 (seq (local 1 {1 ((const i32 1) (const i32 2) (const i32 3))}
                        (seq (const i32 2))))))
  (test-wasm-->> (simple-config
                  (seq (local 1 {1 ((const i32 1) (const i32 2) (const i32 3))}
                         (seq (get-local 1)))))
                 (simple-config
                  (seq (const i32 2))))
  (test-wasm-->> (simple-config
                  (seq (local 1 {1 ((const i32 1) (const i32 2) (const i32 3))}
                         (seq (const i32 42) (tee-local 1)))))
                 (simple-config
                  (seq (const i32 42))))
  (test-wasm-->> (simple-config
                  (seq (local 1 {1 ((const i32 1) (const i32 2) (const i32 3))}
                         (seq trap (get-local 1)))))
                 (simple-config (seq trap)))
  (test-wasm-->> (simple-config
                  (seq (local 1 {1 ((const i32 1) (const i32 2) (const i32 3))}
                         (seq (get-local 1) return (get-local 2)))))
                 (simple-config
                  (seq (const i32 2))))
  (test-wasm-->> (simple-config
                  (seq (local 1 {1 ((const i32 1) (const i32 2) (const i32 3))}
                         (seq (get-local 1) return (get-local 2)))
                       drop))
                 (simple-config (seq)))

  ;; test function calls with factorial
  (let ()
    (define f-0
      (term (func () (-> () (i32)) local () (seq (const i32 0)))))
    (define fact-loop
      (term (func () (-> (i32) (i32)) local (i32)
                  (seq (const i32 1)
                       (set-local 1)
                       (loop (-> () ())
                             (seq (get-local 0)
                                  (eqz i32)
                                  (if (-> () ())
                                      (seq (get-local 1) return)
                                      else
                                      (seq (get-local 0)
                                           (get-local 1)
                                           (mul i32)
                                           (set-local 1)
                                           (get-local 0)
                                           (const i32 1)
                                           (sub i32)
                                           (set-local 0)
                                           (br 1)))))))))
    (define f-2
      (term (func () (-> (i32) (i32)) local ()
                  (seq (const i32 5) (call 1)
                       (get-local 0) (mul i32)))))
    (define cl-0
      (term {(inst 0) (code ,f-0)}))
    (define cl-1
      (term {(inst 0) (code ,fact-loop)}))
    (define cl-2
      (term {(inst 0) (code ,f-2)}))
    (define modinst-0
      (term {(func ,cl-0 ,cl-1 ,cl-2) (glob)}))
    (define modinst-1
      (term {(func) (glob)}))
    (define tabinst-0
      (term ()))
    (define tabinst-1
      (term ()))
    (define func-store
      (term {(inst ,modinst-0 ,modinst-1)
             (tab ,tabinst-0 ,tabinst-1)
             (mem)}))
    (define-syntax-rule (func-config e*)
      (term (,func-store () e* 0)))

    (test-wasm-->> (func-config (seq (call 0)))
                   (func-config (seq (const i32 0))))
    (test-wasm-->> (func-config (seq (const i32 5) (call 1)))
                   (func-config (seq (const i32 120))))
    (test-wasm-->> (func-config (seq (const i32 2) (call 2)))
                   (func-config (seq (const i32 240)))))

  ;; test that globals don't interfere between instances
  (let ()
    (define f-0
      (term (func () (-> () (i32)) local ()
                  (seq (get-global 0)
                       (const i32 1)
                       (add i32)
                       (set-global 0)
                       (get-global 0)
                       return))))
    (define cl-0
      (term {(inst 0) (code ,f-0)}))
    (define cl-1
      (term {(inst 1) (code ,f-0)}))
    (define modinst-0
      (term {(func ,cl-0 ,cl-1) (glob (const i32 42))}))
    (define modinst-1
      (term {(func ,cl-1) (glob (const i32 52))}))
    (define tabinst-0  (term ()))
    (define tabinst-1  (term ()))
    (define func-store
      (term {(inst ,modinst-0 ,modinst-1)
             (tab ,tabinst-0 ,tabinst-1)
             (mem)}))
    (define-syntax-rule (func-config e*)
      (term (,func-store () e* 0)))

    (test-wasm-eval (func-config (seq (call 0) drop (call 0)))
                    (term (const i32 44)))
    (test-wasm-eval (func-config (seq (call 0) (call 0)
                                      drop drop
                                      (call 1)))
                    (term (const i32 53))))

  ;; tests for memory related operations
  (let ()
    ;; f-0 just stores some data
    (define f-0
      (term (func () (-> (i32 i64) ()) local ()
                  (seq (get-local 0)
                       (get-local 1)
                       (store i64 6 0)
                       return))))
    ;; f-1 modifies the data
    (define f-1
      (term (func () (-> (i32 i64) ()) local (i64)
                  (seq (get-local 0)
                       (load i64 6 0)
                       (tee-local 2)
                       (get-local 1)
                       (mul i64)
                       (set-local 2)
                       (get-local 0)
                       (get-local 2)
                       (store i64 6 0)
                       return))))
    ;; f-2 just reads it
    (define f-2
      (term (func () (-> (i32) (i64)) local ()
                  (seq (get-local 0)
                       (load i64 6 0)
                       return))))
    (define cl-0
      (term {(inst 0) (code ,f-0)}))
    (define cl-1
      (term {(inst 1) (code ,f-1)}))
    (define cl-2
      (term {(inst 0) (code ,f-2)}))
    (define modinst-0
      (term {(func ,cl-0 ,cl-1 ,cl-2) (glob) (mem 0)}))
    (define modinst-1
      (term {(func ,cl-1) (glob) (mem 0)}))
    (define mem-store
      (term {(inst ,modinst-0 ,modinst-1)
             (tab () ())
             (mem ,default-memory)}))
    (define-syntax-rule (mem-config e*)
      (term (,mem-store () e* 0)))

    (test-wasm-eval (mem-config (seq (const i32 0)
                                     (const i64 42)
                                     (call 0)
                                     (const i32 0)
                                     (const i64 5)
                                     (call 1)
                                     (const i32 0)
                                     (call 2)))
                    (term (const i64 210)))
    (test-wasm-eval (mem-config (seq current-memory))
                    (term (const i32 1)))
    (test-wasm-eval (mem-config (seq (const i32 2) grow-memory))
                    (term (const i32 3)))
    ;; write/read at very end of page
    (test-wasm-eval (mem-config (seq (const i32 ,(- *page-size* 8))
                                     (const i64 42)
                                     (call 0)
                                     (const i32 ,(- *page-size* 8))
                                     (call 2)))
                    (term (const i64 42)))
    ;; reads & writes out of bounds should fail
    (test-wasm-eval (mem-config (seq (const i32 ,(- *page-size* 7))
                                     (const i64 42)
                                     (call 0)))
                    (term trap))
    (test-wasm-eval (mem-config (seq (const i32 ,(- *page-size* 7))
                                     (call 2)))
                    (term trap))
    )
  )
#lang racket

(require redex)

(define-language wasm-lang
  ;; types
  (t  ::= i32 i64 f32 f64)
  (tp ::= i8 i16 i32)
  (tf ::= (-> (t ...) (t ...)))
  (tg ::= t (mut t))

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
         (load t tp-sx a o)
         (store t a o)
         (store t tp a o)
         current-memory
         grow-memory
         unop-i32
         unop-i64
         unop-f32
         unop-f64
         ;; FIXME: there are more ops
         )
  (e    ::= e-no-v
            (const t c))

  ;; sequences of expressions
  ;; (we use this to avoid splicing)
  (e*   ::= ϵ
            (e e*))

  (c    ::= number)

  ;; constant numerals
  ((i j l k n) integer)

  ;; functions
  (f    ::= (func (ex ...) tf local t ... e ...)
            (func (ex ...) tf im))
  (glob ::= (global (ex ...) tg e ...)
            (global (ex ...) tg im))
  (tab  ::= (table (ex ...) n i ...)
            (table (ex ...) n im))
  (mem  ::= (memory (ex ...) n)
            (memory (ex ...) n im))
  (im   ::= (import string string))
  (ex   ::= (export string))
  (m    ::= (module f ... glob ...)
            (module f ... glob ... tab)
            (module f ... glob ... mem)
            (module f ... glob ... tab mem)))

(define-extended-language wasm-runtime-lang wasm-lang
  ;; administrative expressions
  (e-no-v  ::= ....
               trap
               (call cl)
               (label n {e*} e*)
               (local n {i (v ...)} e*))

  ;; runtime
  (s       ::= {(modinst ...) (tabinst ...) (meminst ...)})
  (modinst ::= {(func cl ...) (global v ...)}
               {(func cl ...) (global v ...) (tab i)}
               {(func cl ...) (global v ...) (mem i)}
               {(func cl ...) (global v ...) (tab i) (mem i)})
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

(define wasm->
  (reduction-relation
   wasm-runtime-lang
   (--> (s F (trap (e e*)) i)
        (s F (trap ϵ) i)
        trap)
   (--> (s F (in-hole E (trap e*)) i)
        (s F (trap ϵ) i)
        (side-condition (not (redex-match wasm-runtime-lang hole (term E))))
        trap-context)

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

        (where e_lbl         (label l {(seq e_loop ϵ)} (in-hole E_v e*_0)))
        (where l             ,(length (term (t_2 ...))))
        (where k             ,(length (term (t_1 ...))))
        (where (E_outer E_v) (v-split E k))
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

   #;
   (--> (s (v ...) (in-hole E ((call j) e*)))
        (s (v ...) (in-hole E ((call (s-func s i j)) e*)))
        call-index)
   ;; TODO: call, call-indirect

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
        (s F (in-hole E ((read-glob s i j) e*)) i)
        get-global)

   (--> (s F (in-hole E (v ((set-global j) e*))) i)
        (s_new F (in-hole E e*) i)
        (where s_new (write-glob s i j v))
        set-global)

   ;; reductions for operating on memory
   (--> (s F (in-hole E ((const i32 k) ((load t a o) e*))) i)
        ;; TODO: define reinterpret
        (s F (in-hole E ((const t (reinterpret t b)) e*)) i)
        (where b (s-mem i ,(+ (term k) (term o))))
        load)
   ;; TODO: load tp-sx case, store

   (--> (s F (in-hole E (current-memory e*)) i)
        ;; TODO: define memory-size
        (s F (in-hole E ((const i32 (memory-size s i)) e*)) i)
        current-memory)

   ;; TODO: fail case
   (--> (s F (in-hole E ((const i32 k) (grow-memory e*))) i)
        (s_new F (in-hole E ((const i32 j_newsize) e*)) i)
        ;; TODO: define expand-memory
        (where (s_new j_newsize) (expand-memory s i k))
        grow-memory)

   with
   [(--> (s F (in-hole E a) i)
         (s F (in-hole E b) i))
    (==> a b)]
   [(--> (s F a i)
         (s F b i))
    (++> a b)]))

(module+ test
  (require rackunit)

  (define-syntax-rule (test-wasm--> x y)
    (test--> wasm-> x y))
  (define-syntax-rule (test-wasm-->> x y)
    (test-->> wasm-> x y))

  ;; test helpers and terms
  (define mt-s (term {() () ()}))
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
  )
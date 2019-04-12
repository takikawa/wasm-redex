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
  ((l k n) integer)

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
               (local n {i v ...} e*))

  ;; runtime
  (s       ::= {(modinst ...) (tabinst ...) (meminst ...)})
  (modinst ::= {(func cl ...) (glob v ...)}
               {(func cl ...) (glob v ...) (tab i)}
               {(func cl ...) (glob v ...) (mem i)}
               {(func cl ...) (glob v ...) (tab i) (mem i)})
  (tabinst ::= (cl ...))
  (meminst ::= (b ...))
  (cl      ::= {(inst i) (code f)})

  (v       ::= (const t c))
  (v*      ::= ϵ
               (v v*))

  ;; evaluation contexts
  ;; using an inductive definition instead of using sequences because
  ;; we would need splicing holes otherwise
  (Ev      ::= hole
               (v Ev))
  (E       ::= Ev
               (label n (e ...) E)))

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

(define-metafunction wasm-runtime-lang
  v-depth : E -> number
  [(v-depth hole) 0]
  [(v-depth (v E)) ,(add1 (term (v-depth E)))]
  ;; TODO: case for label
  )

(module+ test
  (test-equal (term (v-depth hole)) (term 0))
  (test-equal (term (v-depth ((const i32 2) ((const i32 1) hole))))
              (term 2)))

(define-metafunction wasm-runtime-lang
  v-split : E number -> (E E)
  [(v-split E l)
   (hole E)
   (side-condition (= (term (v-depth E)) (term l)))]
  [(v-split (name E_0 (v E_1)) l)
   ((v E_outer) E_v)
   (where (E_outer E_v) (v-split E_1 l))
   (side-condition (> (term (v-depth E_0)) (term l)))]
  ;; TODO: case for label
  )

(module+ test
  (test-equal (term (v-split hole 0))
              (term (hole hole)))
  (test-equal (term (v-split ((const i32 2) ((const i32 1) hole)) 1))
              (term (((const i32 2) hole)
                     ((const i32 1) hole))))
  )

(define wasm->
  (reduction-relation
   wasm-runtime-lang
   ;; generally these rules need to mention the "continuation" in the sequence
   ;; of instructions because Redex does not allow splicing holes with a
   ;; sequence of s-exps
   (==> (unreachable e*) (trap e*))
   (==> (v (drop e*)) e*)
   (==> (nop e*) e*)

   (==> (v_1 (v_2 ((const i32 0) (select e*))))
        (v_2 e*)
        select-false)
   (==> (v_1 (v_2 ((const i32 k) (select e*))))
        (v_1 e*)
        (side-condition (>= (term k) 1))
        select-true)

   (==> ((label n {e*_0} v*) e*_1)
        (e*-append v* e*_1)
        label-value)
   (==> ((label n {e*_0} trap) e*_1)
        (trap e*_1)
        label-trap)

   ;; Redex can't express a pattern like n-level nestings of an
   ;; expression, so we explicitly compute the nesting depth of
   ;; values around the hole in the context E instead
   (++> (in-hole E ((block (-> (t_1 ...) (t_2 ...)) e*_0) e*_1))
        (in-hole E_outer (seq* (label l {ϵ} (in-hole E_v e*_0)) e*_1))
        (where l ,(length (term (t_2 ...))))
        (where k ,(length (term (t_1 ...))))
        (where (E_outer E_v) (v-split E k))
        block)

   ;; TODO: loop

   (==> ((const i32 0) ((if tf e*_1 else e*_2) e*))
        (seq* (block tf e*_2) e*)
        if-false)
   (==> ((const i32 k) ((if tf e*_1 else e*_2) e*))
        (seq* (block tf e*_1) e*)
        (side-condition (>= (term k) 1))
        if-true)

   with
   [(--> (s (v ...) (in-hole E a))
         (s (v ...) (in-hole E b)))
    (==> a b)]
   [(--> (s (v ...) a)
         (s (v ...) b))
    (++> a b)]))

(module+ test
  (require rackunit)

  (define-syntax-rule (test-wasm--> x y)
    (test--> wasm-> x y))
  (define-syntax-rule (test-wasm-->> x y)
    (test-->> wasm-> x y))

  ;; test helpers and terms
  (define mt-s (term {() () ()}))
  (define-syntax-rule (simple-config e)
    (term (,mt-s () e)))

  ;; sanity checks for the grammar
  (check-not-false
   (redex-match wasm-runtime-lang s mt-s))
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

  ;; test block & related constructs
  (test-wasm--> (simple-config
                 (seq (const i32 1) (const i32 2) (block (-> (i32) (i32)) ϵ)))
                (simple-config
                 (seq (const i32 1) (label 1 {ϵ} ((const i32 2) ϵ)))))
  (test-wasm-->> (simple-config (seq (const i32 1) (const i32 2) (block (-> (i32) (i32)) ϵ)))
                 (simple-config (seq (const i32 1) (const i32 2))))
  )
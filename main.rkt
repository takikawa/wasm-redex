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
         (block tf e ...)
         (loop tf e ...)
         (if tf e ... else e ...)
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

  (c    ::= number)

  ;; constant numerals
  (n    ::= integer)
  (k    ::= integer)

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
               (label n (e ...) e)
               (local n (i v ...) e ...))

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

  ;; evaluation contexts
  ;; using an inductive definition instead of using sequences because
  ;; we would need splicing holes otherwise
  (e*      ::= ϵ
               (e e*))
  (Ee      ::= ϵ
               (e-no-v Ee))
  (Ev      ::= (hole Ee)
               (v Ev))
  (E       ::= hole
               Ev
               (label n (e ...) E)))

;; helper for constructing instruction sequences
(define-metafunction wasm-runtime-lang
  seq : e ... -> e*
  [(seq) ϵ]
  [(seq e_0 e_1 ...)
   (e_0 (seq e_1 ...))])

(define wasm->
  (reduction-relation
   wasm-runtime-lang
   ;; generally these rules need to mention the "continuation" in the sequence
   ;; of instructions because of Redex does not allow splicing holes with a
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

   with
   [(--> (s (v ...) (in-hole E a))
         (s (v ...) (in-hole E b)))
    (==> a b)]))

(module+ test
  (require rackunit)

  (define-syntax-rule (test-wasm--> x y)
    (test--> wasm-> x y))

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

  (test-wasm--> (simple-config (seq (const i32 42) drop))
                (simple-config (seq)))
  (test-wasm--> (simple-config (seq (const i32 1) (const i32 2) (const i32 0) select))
                (simple-config (seq (const i32 2))))
  (test-wasm--> (simple-config (seq (const i32 1) (const i32 2) (const i32 42) select))
                (simple-config (seq (const i32 1)))))
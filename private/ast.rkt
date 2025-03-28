;; Copyright 2024-2025 Ryan Culpepper
;; SPDX-License-Identifier: Apache-2.0

#lang racket/base
(require racket/match
         racket/list
         racket/string)
(provide (all-defined-out))

(struct setdecl (s elems) #:prefab)
(struct axiom (n p) #:prefab)
(struct setgoal (prop) #:prefab)
(struct line (n s) #:prefab)
(struct qed () #:prefab)

(struct derive (p j) #:prefab)
(struct block (rule ss) #:prefab)
(struct assume (p) #:prefab)
(struct intro (vs s) #:prefab)
(struct want (p) #:prefab)

(struct prop:not (p) #:prefab)
(struct prop:and (p q) #:prefab)
(struct prop:or (p q) #:prefab)
(struct prop:implies (p q) #:prefab)
(struct prop:iff (p q) #:prefab)
(struct prop:forall (v s p) #:prefab)
(struct prop:exists (v s p) #:prefab)
(struct prop:atomic (a) #:prefab)

(struct prop:eq (a b) #:prefab)
(struct prop:cmp (cmp a b) #:prefab)
(struct prop:pred (pred args) #:prefab)
(struct prop:in (e s) #:prefab)

(define (prop? v)
  (or (prop:not? v) (prop:and? v) (prop:or? v) (prop:implies? v) (prop:iff? v)
      (prop:forall? v) (prop:exists? v) (prop:atomic? v)
      (prop:eq? v) (prop:cmp? v) (prop:pred? v) (prop:in? v)))

(struct expr:integer (n) #:prefab)
(struct expr:object (s) #:prefab)
(struct expr:var (var) #:prefab)
(struct expr:plus (a b) #:prefab)
(struct expr:times (a b) #:prefab)
(struct expr:apply (fun args) #:prefab)

(struct j:AndElimL (p) #:prefab)
(struct j:AndElimR (p) #:prefab)
(struct j:AndIntro (p q) #:prefab)
(struct j:OrElim (pq hp hq) #:prefab)
(struct j:OrIntroL (p) #:prefab)
(struct j:OrIntroR (p) #:prefab)
(struct j:ImpElim (pq p) #:prefab)
(struct j:ImpIntro (b) #:prefab)
(struct j:IffElimF (p) #:prefab)
(struct j:IffElimB (p) #:prefab)
(struct j:IffIntro (f b) #:prefab)
(struct j:ForallElim (p vm) #:prefab)
(struct j:ForallIntro (b) #:prefab)
(struct j:ExistsElim (p b) #:prefab)
(struct j:ExistsIntro (p vm) #:prefab)
(struct j:elim (p vm dir qs) #:prefab)
(struct j:intro (b) #:prefab)
(struct j:algebra (ps) #:prefab)
(struct j:ModusTollens (pq nq) #:prefab)
(struct j:DisjSyl (pq np) #:prefab)
(struct j:Contradiction (b) #:prefab)
(struct j:Repeat (p) #:prefab)

(struct ref:line (ln) #:prefab)
(struct ref:axiom (n) #:prefab)

;; ============================================================

(define (prop->string p)
  (let loop ([p p])
    (match p
      [(prop:not p) (format "¬~a" (loop p))]
      [(prop:and p q) (format "(~a ∧ ~a)" (loop p) (loop q))]
      [(prop:or p q) (format "(~a ∨ ~a)" (loop p) (loop q))]
      [(prop:implies p q) (format "(~a ⇒ ~a)" (loop p) (loop q))]
      [(prop:iff p q) (format "(~a ⇔ ~a)" (loop p) (loop q))]
      [(prop:forall v s p) (format "(∀ ~a ∈ ~a, ~a)" (var->string v) s (loop p))]
      [(prop:exists v s p) (format "(∃ ~a ∈ ~a, ~a)" (var->string v) s (loop p))]
      [(prop:atomic a) (format "~a" a)]
      [(prop:eq a b) (format "(~a = ~a)" (expr->string a) (expr->string b))]
      [(prop:cmp cmp a b) (format "(~a ~a ~a)" (expr->string a) (cmp->string cmp) (expr->string b))]
      [(prop:pred pred args)
       (format "~a(~a)" pred (string-join (map expr->string args) ", "))]
      [(prop:in e s) (format "(~a ∈ ~a)" (expr->string e) s)]
      [_ (error 'prop->string "internal error: bad prop: ~e" p)])))

(define (cmp->string cmp)
  (case cmp [(gt) ">"] [(ge) "≥"] [(lt) "<"] [(le) "≤"]))

(define (expr->string e)
  (match e
    [(expr:integer n) (format "~a" n)]
    [(expr:object s) (format "'~a'" s)]
    [(expr:var var) (format "~a" var)]
    [(expr:plus a b) (format "(~a + ~a)" (expr->string a) (expr->string b))]
    [(expr:times a b) (format "(~a * ~a)" (expr->string a) (expr->string b))]
    [(expr:apply fun args)
     (format "~a(~a)" fun (string-join (map expr->string args) ", "))]
    [_ (error 'expr->string "internal error: bad expr: ~e" e)]))

(define (var->string v) (symbol->string v))

(define (vars->string vs [tight? #f])
  (string-join (map var->string vs) (if tight? "," ", ")))

(define (exprs->string es)
  (string-join (map expr->string es) ", "))

(define (lineno->string ln)
  (string-join (map number->string ln) "."))

;; ----------------------------------------

(define (prop-fvs p env)
  (let loop ([p p])
    (match p
      [(prop:not p) (loop p)]
      [(prop:and p q) (append (loop p) (loop q))]
      [(prop:or p q) (append (loop p) (loop q))]
      [(prop:implies p q) (append (loop p) (loop q))]
      [(prop:iff p q) (append (loop p) (loop q))]
      [(prop:forall v s body) (prop-fvs body (hash-set env v s))]
      [(prop:exists v s body) (prop-fvs body (hash-set env v s))]
      [(prop:atomic a) null]
      [(prop:eq a b) (append (expr-fvs a env) (expr-fvs b env))]
      [(prop:cmp cmp a b) (append (expr-fvs a env) (expr-fvs b env))]
      [(prop:pred pred args) (exprs-fvs args env)]
      [(prop:in e s) (expr-fvs e env)]
      [_ (error 'prop-fvs "internal error: bad prop: ~e" p)])))

(define (expr-fvs e env)
  (let loop ([e e])
    (match e
      [(expr:integer n) null]
      [(expr:object s) null]
      [(expr:var var) (if (hash-has-key? env var) null (list var))]
      [(expr:plus a b) (append (loop a) (loop b))]
      [(expr:times a b) (append (loop a) (loop b))]
      [(expr:apply fun args) (exprs-fvs args env)])))

(define (exprs-fvs es env)
  (append* (for/list ([e (in-list es)]) (expr-fvs e env))))

;; ----------------------------------------

;; all-names : Hasheq[Symbol => #t]
;; Set by check-proof.
(define all-names (make-parameter (hasheq)))

;; in-scope : Hasheq[Symbol => Symbol] -- variable to set name
(define in-scope (make-parameter (hasheq)))

(define (prop-subst p vm)
  (define vmfv (exprs-fvs (map cdr vm) (hasheq)))
  (let loop ([p p])
    (match p
      [(prop:not p) (prop:not (loop p))]
      [(prop:and p q) (prop:and (loop p) (loop q))]
      [(prop:or p q) (prop:or (loop p) (loop q))]
      [(prop:implies p q) (prop:implies (loop p) (loop q))]
      [(prop:iff p q) (prop:iff (loop p) (loop q))]
      [(prop:forall v s body)
       (binder-subst prop:forall v s body vm vmfv)]
      [(prop:exists v s body)
       (binder-subst prop:exists v s body vm vmfv)]
      [(prop:atomic a) p]
      [(prop:eq a b) (prop:eq (expr-subst a vm) (expr-subst b vm))]
      [(prop:cmp cmp a b) (prop:cmp cmp (expr-subst a vm) (expr-subst b vm))]
      [(prop:pred pred args)
       (prop:pred pred (for/list ([arg (in-list args)]) (expr-subst arg vm)))]
      [(prop:in e s) (prop:in (expr-subst e vm) s)]
      [_ (error 'prop-subst "internal error: bad prop: ~e" p)])))

(define (binder-subst constructor v s body vm0 vmfv)
  (define vm (filter (lambda (vme) (not (eq? (car vme) v))) vm0))
  (define v* (if (memq v vmfv) (fresh v) v))
  (cond [(equal? v v*)
         (constructor v s (prop-subst body vm))]
        [else
         (define vm* (list (cons v (expr:var v*))))
         (define body* (prop-subst body vm*))
         (constructor v* s (prop-subst body* vm))]))

(define (expr-subst e vm)
  (let loop ([e e])
    (match e
      [(expr:integer n) e]
      [(expr:object s) e]
      [(expr:var var)
       (cond [(assq var vm) => cdr]
             [else e])]
      [(expr:plus a b) (expr:plus (loop a) (loop b))]
      [(expr:times a b) (expr:times (loop a) (loop b))]
      [(expr:apply fun args) (expr:apply fun (map loop args))])))

(define (fresh v)
  (define venv (in-scope))
  (define names (all-names))
  (let loop ([i 1])
    (define vi (string->symbol (format "~a_~a" v i)))
    (cond [(hash-has-key? venv vi) (loop (add1 i))]
          [(hash-has-key? names vi) (loop (add1 i))]
          [else (all-names (hash-set names vi #t)) vi])))

;; ----------------------------------------

(define (expr-in-set-elems? e env elems)
  (match e
    [(expr:integer n)
     (and (or (member n elems) (member 'nat elems)) #t)]
    [(expr:object s) (and (member s elems) #t)]
    [(expr:var var)
     (for/and ([velem (in-list (hash-ref env var))])
       (and (member velem elems) #t))]
    [(expr:plus a b)
     (and (expr-in-set-elems? a env '(nat))
          (expr-in-set-elems? a env '(nat))
          (memq 'nat elems) #t)]
    [(expr:times a b)
     (and (expr-in-set-elems? a env '(nat))
          (expr-in-set-elems? a env '(nat))
          (memq 'nat elems) #t)]
    [(expr:apply fun args) #f] ;; FIXME
    [_ #f]))

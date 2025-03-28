;; Copyright 2024-2025 Ryan Culpepper
;; SPDX-License-Identifier: Apache-2.0

#lang racket/base
(require (for-syntax racket/base)
         racket/list
         racket/match
         racket/string
         parser-tools/yacc
         parser-tools/lex
         (prefix-in : parser-tools/lex-sre)
         "private/ast.rkt"
         "private/error.rkt"
         "private/parse.rkt")
(provide (all-from-out "private/ast.rkt")
         (all-from-out "private/error.rkt")
         string->proof
         string->prop
         (struct-out proof)
         (struct-out cstate)
         check-proof)

;; ============================================================

;; CheckState
(struct cstate
  (prefix ;; LineNoPrefix
   bs     ;; BlockState
   goals  ;; #f or (Listof Prop) -- Wants that have not been discharged
   last   ;; (U #f Derive Assume CheckState) -- last stmt or state of last Block
   ) #:transparent)

(define (cstate-update cs #:bs [bs #f] #:want [want #f] #:have [have #f] #:last [newlast #f])
  (match-define (cstate prefix bstate goals last) cs)
  (let ([goals (and goals (if have (remove* (list have) goals) goals))]
        [last (if want #f last)])
    (cstate prefix (or bs bstate) (if want (cons want (or goals null)) goals) (or newlast last))))

;; LEnv = Hash
;; - maps AxiomRef to Prop
;; - maps LineNo to Statement
;; - maps Symbol to (Listof (U String Nat 'nat)) --- set name to elements
(define base-lenv (hash 'ℕ (list 'nat)))

;; FIXME: set all-names

;; check-proof : Proof -> CheckState
;; Returns prop for complete proof (ends in Derive), #f otherwise.
(define (check-proof pf)
  (match pf
    [(proof decls goal lines qed?)
     (define lenv (check-decls decls))
     (when goal
       (parameterize ((error-info (cons (err:in-theorem) (error-info))))
         (check-wf-prop goal lenv)))
     (define cs (check-block lines lenv 'top null #t))
     (when qed?
       (define last-derived-prop ;; FIXME: =? (cstate-last cs)
         (match (and (pair? lines) (last lines))
           [(line ln (derive p _)) p]
           [_ #f]))
       (unless last-derived-prop
         (reject
          `(v (h "Incorrect proof (QED failed).")
              (p "The proof is incomplete, because the main proof list"
                 "does not end with a Derive statement."))))
       (unless (prop=? goal last-derived-prop)
         (reject
          `(v (h "Incorrect proof (QED failed).")
              (p "The last proposition derived by the proof is not"
                 "the proposition from the Theorem declaration.")
              (h "Theorem: " ,(rich 'prop goal))
              (h "Last derived: " ,(rich 'prop last-derived-prop))))))
     cs]))

(define (check-decls decls)
  (for/fold ([lenv base-lenv]) ([decl (in-list decls)])
    (match decl
      [(setdecl s elems)
       (hash-set lenv s elems)]
      [(axiom n p)
       (let ([fvs (prop-fvs p (hasheq))])
         (unless (null? fvs)
           (reject (err:prop-fv (ref:axiom n) fvs))))
       (hash-set lenv (ref:axiom n) p)])))

(define (check-block lines lenv b-rule lnprefix last?)
  (define cs (cstate lnprefix (block-rule->state b-rule) #f #f))
  (check-lines lines lenv b-rule cs last?))

(define (check-lines lines lenv b-rule cs last?)
  (match lines
    [(list)
     cs]
    [(cons (line n stmt) lines)
     (define cs*
       (parameterize ((error-info (list (err:on-line n stmt))))
         (check-statement n stmt lenv b-rule cs (and last? (null? lines)))))
     (check-lines lines (hash-set lenv n stmt) b-rule cs* last?)]))

;; check-statement : LineNo Statement LEnv BlockRule CheckState Boolean -> CheckState
;; Returns list of special statement types allowed *after* this statement.
(define (check-statement n stmt lenv b-rule cs last?)
  (match stmt
    [(derive prop just)
     (begin0 (cstate-update cs
                            #:bs (block-state-check/advance cs b-rule 'derive)
                            #:have prop #:last stmt)
       (check-wf-prop prop lenv)
       (check-derive n prop just lenv))]
    [(want prop)
     (begin0 (cstate-update cs
                            #:bs (block-state-check/advance cs b-rule 'want)
                            #:want prop)
       (check-wf-prop prop lenv))]
    [(assume prop)
     (begin0 (cstate-update cs
                            #:bs (block-state-check/advance cs b-rule 'assume)
                            #:have prop #:last stmt)
       (check-wf-prop prop lenv))]
    [(intro vars s)
     (define stype (if (= (length vars) 1) 'intro1 'intro*))
     (begin0 (cstate-update cs #:bs (block-state-check/advance cs b-rule stype))
       (cond [(hash-ref lenv s #f)
              => (lambda (elems)
                   (for ([var (in-list vars)])
                     (when (hash-has-key? (in-scope) var)
                       (reject (err:intro-not-fresh var)))
                     (in-scope (hash-set (in-scope) var elems))))]
             [else (reject (err:not-declared-set s))]))]
    [(block rule lines)
     (define bs* (block-state-check/advance cs b-rule 'block))
     (parameterize ((in-scope (in-scope))) ;; mutated by Intro
       (define sub-cs (check-block lines lenv rule n last?))
       (unless last?
         ;; Only check how block ends if nothing follows it, because
         ;; otherwise it would interfere with checking partial proofs.
         (block-state-check/advance sub-cs rule 'end))
       (cstate-update cs #:bs bs* #:last sub-cs))]))

(define (check-wf-prop prop lenv)
  ;; Check no free variables
  (let ([fvs (prop-fvs prop (in-scope))])
    (unless (null? fvs)
      (reject (err:prop-fv #f fvs))))
  ;; Check set names FIXME
  (void))

(define (block-rule->state rule)
  (case rule
    [(forall) 'i-d*]
    [(exists) 'i-a-d*]
    [(implies) 'a-d*]
    [(contradiction) 'a-d*]
    [(top) 'd*]
    [(#f) 'I/a-a*-d*]))

;; BlockRule = #f | 'forall | 'exists | 'implies | 'contradiction
;; BlockState
;; - 'I/a-a*-d*
;; - 'i-a-d*
;; - 'i-d*
;; - 'a-d*
;; - 'a*-d*
;; - 'd*    -- last statement was not Derive
;; - 'd:d*  -- last statement was Derive

(define (block-state-check/advance cs b-rule stype)
  (define state (cstate-bs cs))
  (match stype
    ['intro1
     (define not-allowed "Let statement is not allowed here.")
     (match state
       ['I/a-a*-d* 'a*-d*]
       ['i-a-d* 'a-d*]
       ['i-d* 'd*]
       [_ (reject `(v ,not-allowed
                      ,@(err:block-misplaced 'intro state b-rule)
                      ,@(err:block-wanted state b-rule)))])]
    ['intro*
     (define not-allowed "Let statement is not allowed here.")
     (match state
       ['I/a-a*-d* 'a*-d*]
       [(or 'i-a-d* 'i-d*)
        (reject `(v "Let statement with multiple variables is not allowed here."
                    "The rule requires a Let statement with a single variable."))]
       [_ (reject `(v ,not-allowed
                      ,@(err:block-misplaced 'intro state b-rule)
                      ,@(err:block-wanted state b-rule)))])]
    ['assume
     (define not-allowed "Assume statement is not allowed here.")
     (match state
       ['I/a-a*-d* 'a*-d*]
       ['a-d* 'd*]
       ['a*-d* 'a*-d*]
       [_ (reject `(v ,not-allowed
                      ,@(err:block-misplaced 'assume state b-rule)
                      ,@(err:block-wanted state b-rule)))])]
    ['want
     (match state
       ['d:d* 'd*]
       [_ state])]
    ['block
     (define not-allowed "Block statement is not allowed here.")
     (match state
       [(or 'a*-d* 'd:d* 'd*) 'd*]
       [_ (reject `(v ,not-allowed
                      ,@(err:block-misplaced stype state b-rule)
                      ,@(err:block-wanted state b-rule)))])]
    ['derive
     (define not-allowed "Derive statement is not allowed here.")
     (match state
       [(or 'a*-d* 'd* 'd:d*) 'd:d*]
       [_ (reject `(v ,not-allowed
                      ,@(err:block-misplaced stype state b-rule)
                      ,@(err:block-wanted state b-rule)))])]
    ['end
     (define not-allowed
       `(h "Block for " ,(rich 'rule (block-rule-name b-rule)) " is incomplete."))
     (match state
       ['I/a-a*-d* (reject `(v ,not-allowed (h "Expected a Let or Assume statement next.")))]
       [(or 'i-a-d* 'i-d*) (reject `(v ,not-allowed (h "Expected a Let statement next.")))]
       ['a-d* (reject `(v ,not-allowed (h "Expected an Assume statement next.")))]
       ['a*-d* (reject `(v ,not-allowed
                           (h "Expected an Assume or Derive statement next.")
                           (h "The block must end with a Derive statement.")))]
       ['d* (reject `(v ,not-allowed
                        (h "The block must end with a Derive statement.")))]
       ['d:d* 'd:d*])]
    ))

(define (block-rule-name state)
  (match state
    ['forall "∀Intro"]
    ['exists "∃Elim"]
    ['implies "⇒Intro"]
    ['contradiction "Contradiction"]
    ['intro "Intro"]
    [#f "Intro"]))

(define (err:block-misplaced stype state b-rule)
  (match stype
    ['intro
     (cond [(memq b-rule '(top))
            '("A Let statement must be within a block.")]
           [(memq b-rule '(#f forall exists))
            '("A Let statement must be the first statement of a block.")]
           [else null])]
    ['assume
     (cond [(memq b-rule '(top))
            '("An Assume statement must be within a block.")]
           [else null])]
    [_ null]))

(define (err:block-wanted state b-rule)
  (match state
    ['i/a-a*-d*
     (list `(p "Expected either a Let statement or Assume statement here."))]
    [(or 'i-a-d* 'i-d*)
     (list `(p "A block for " ,(rich 'rule (block-rule-name b-rule))
               " should have a Let statement here."))]
    ['a-d*
     (list `(p "A block for " ,(rich 'rule (block-rule-name b-rule))
               " should have an Assume statement here."))]
    [(or 'a*-d* 'd*) null]))

(define (n->nth n)
  (case n
    [(1) "first"]
    [(2) "second"]
    [(3) "third"]
    [(4) "fourth"]
    [(5) "fifth"]))

(define (justification-rule-name j)
  (match j
    [(j:AndElimL _) "∧ElimL"]
    [(j:AndElimR _) "∧ElimR"]
    [(j:AndIntro p q) "∧Intro"]
    [(j:OrElim pq hp hq) "∨Elim"]
    [(j:OrIntroL p) "∨IntroL"]
    [(j:OrIntroR q) "∨IntroR"]
    [(j:ImpElim pq p) "⇒Elim"]
    [(j:ImpIntro b) "⇒Intro"]
    [(j:IffElimF p) "⇔ElimF"]
    [(j:IffElimB p) "⇔ElimB"]
    [(j:IffIntro f b) "⇔Intro"]
    [(j:ForallElim p vm) "∀Elim"]
    [(j:ForallIntro b) "∀Intro"]
    [(j:ExistsElim p b) "∃Elim"]
    [(j:ExistsIntro p vm) "∃Intro"]
    [(j:elim p vm dir qs) "Relaxed Elimination"]
    [(j:intro b) "Relaxed Introduction"]
    [(j:algebra _) "Algebra"]
    [(j:ModusTollens _ _) "Modus Tollens"]
    [(j:DisjSyl _ _) "Disjunctive Syllogism"]
    [(j:Contradiction _) "Contradiction"]
    [(j:Repeat _) "Repeat"]
    [_ #f]))

;; ----------------------------------------

(define (check-derive at prop just lenv)
  (parameterize ((error-info (cons (err:rule just) (error-info))))
    (check-derive* at prop just lenv)))

(define (check-derive* at prop just lenv)
  (define (getln ln)
    (unless (lineno-avail? ln at)
      (reject (err:ref-line-unavail ln)))
    (hash-ref lenv ln #f))
  (define (getp r)
    (match r
      [(ref:axiom n)
       (or (hash-ref lenv (ref:axiom n) #f)
           (reject (err:ref-axiom-undef r)))]
      [(ref:line ln)
       (match (getln ln)
         [(assume p) p]
         [(derive p j) p]
         [(want _) (reject (err:ref-is-want r))]
         [(block _ _) (reject (err:ref-is-block r))]
         [(intro _ _) (reject (err:ref-is-intro r))]
         [_ (error* "internal error: bad proposition reference")])]))
  (define (getb r)
    (match r
      [(ref:axiom _)
       (reject (err:ref-not-block r))]
      [(ref:line ln)
       (match (getln ln)
         [(? block? b) b]
         [_ (reject (err:ref-not-block r))])]))
  (define (bad argn got-p form [mvenv '()] [mvwhy #f]
               #:more [more null]
               #:expect [expected #f])
    (define what
      (cond [argn `(h "The rule's " ,(n->nth argn) " argument")]
            [else "An intermediate result"]))
    (reject (err:incorrect-prop what got-p form mvenv mvwhy more expected)))
  (define (badr [form #f] [mvenv '()] [mvwhy #f]
                #:more [more null]
                #:expect [expected #f])
    (define what "The rule's result")
    (reject (err:incorrect-prop what prop form mvenv mvwhy more expected)))
  (match just
    ;; ----------------------------------------
    [(j:AndElimL (app getp pq))
     (define-values (p q)
       (match pq
         [(prop:and p q) (values p q)]
         [_ (bad 1 pq "p ∧ q")]))
     (unless (prop=? prop p)
       (badr "p" `((p ,p) (q ,q)) 'arg #:expect p))]
    [(j:AndElimR (app getp pq))
     (define-values (p q)
       (match pq
         [(prop:and p q) (values p q)]
         [_ (bad 1 pq "p ∧ q")]))
     (unless (prop=? prop q)
       (badr "q" `((p ,p) (q ,q)) 'arg #:expect p))]
    [(j:AndIntro (app getp p) (app getp q))
     (define dprop (prop:and p q))
     (unless (prop=? prop dprop)
       (badr "p ∧ q" `((p ,p) (q ,q)) 'args #:expect dprop))]
    ;; ----------------------------------------
    [(j:OrElim (app getp pq) (app getp hp) (app getp hq))
     (define-values (p q)
       (match pq
         [(prop:or p q) (values p q)]
         [_ (bad 1 pq "p ∨ q")]))
     (define r
       (match hp
         [(prop:implies pp r) #:when (prop=? pp p) r]
         [_ (bad 2 hp "p ⇒ r" `((p ,p) (q ,q)) 'prev)]))
     (match hq
       [(prop:implies qq rr) #:when (and (prop=? qq q) (prop=? rr r)) (void)]
       [_ (bad 3 hq "q ⇒ r" `((p ,p) (q ,q) (r ,r)) 'prev)])
     (unless (prop=? prop r)
       (badr "r" `((p ,p) (q ,q) (r ,r)) 'args #:expect r))]
    [(j:OrIntroL (app getp p))
     (match prop
       [(prop:or pp qq) #:when (prop=? pp p) (void)]
       [_ (badr "p ∨ q" `((p ,p)) 'arg)])]
    [(j:OrIntroR (app getp q))
     (match prop
       [(prop:or pp qq) #:when (prop=? qq q) (void)]
       [_ (badr "p ∨ q" `((q ,q)) 'arg)])]
    ;; ----------------------------------------
    [(j:ImpElim (app getp pq) (app getp p))
     (define-values (pp qq)
       (match pq
         [(prop:implies pp qq) (values pp qq)]
         [_ (bad 1 pq "p ⇒ q")]))
     (unless (prop=? pp p)
       (bad 2 p "p" `((p ,pp) (q ,qq)) 'prev #:expect pp))
     (unless (prop=? prop qq)
       (badr "q" `((p ,pp) (q ,qq)) 'args #:expect qq))]
    [(j:ImpIntro (and b-ref (app getb b)))
     ;; Block checks: no intros, one assumption, ends with derive
     (define-values (intros assumes lastd) (split-block b 'implies b-ref))
     (define pa (match assumes [(list (assume pa)) pa]))
     (define pz (match lastd [(derive p _) p]))
     (define dprop (prop:implies pa pz))
     (unless (prop=? prop dprop)
       (badr "p ⇒ q" `((p ,pa) (q ,pz)) 'arg #:expect dprop))]
    ;; ----------------------------------------
    [(j:IffElimF (app getp pq))
     (define-values (p q)
       (match pq
         [(prop:iff p q) (values p q)]
         [_ (bad 1 pq "p ⇔ q")]))
     (define dprop (prop:implies p q))
     (unless (prop=? prop dprop)
       (badr "p ⇒ q" `((p ,p) (q ,q)) 'arg #:expect dprop))]
    [(j:IffElimB (app getp pq))
     (define-values (p q)
       (match pq
         [(prop:iff p q) (values p q)]
         [_ (bad 1 pq "p ⇔ q")]))
     (define dprop (prop:implies q p))
     (unless (prop=? prop dprop)
       (badr "q ⇒ p" `((p ,p) (q ,q)) 'arg #:expect dprop))]
    [(j:IffIntro (app getp f) (app getp b))
     (match prop
       [(prop:iff p q)
        (unless (prop=? f (prop:implies p q))
          (bad 1 f "p ⇒ q" `((p ,p) (q ,q)) 'res #:expect (prop:implies p q)))
        (unless (prop=? b (prop:implies q p))
          (bad 2 b "q ⇒ p" `((p ,p) (q ,q)) 'res #:expect (prop:implies q p)))]
       [_ (badr "p ⇔ q")])]
    ;; ----------------------------------------
    [(j:ForallElim (app getp p) vm)
     (match vm
       [(list (cons vmv vme))
        (match p
          [(prop:forall v s body)
           (unless (equal? v vmv)
             (reject (err:vm-var v vmv)))
           (check-vm-expr vme s lenv)
           (define body* (prop-subst body vm))
           (unless (prop=? prop body*)
             (badr "P(a)"
                   #:more `[" where (if the rule's arguments are correct):"
                            (h "  " ,(rich 'pattern "P(x)") " = " ,(rich 'prop body))
                            (h "  " ,(rich 'pattern "x") " = " ,(rich 'var vmv))
                            (h "  " ,(rich 'pattern "a") " = " ,(rich 'expr vme))]
                   #:expect body*))]
          [_ (bad 1 p "∀ x ∈ S, P(x)")])]
       [_ (reject (err:vm-multi vm))])]
    [(j:ForallIntro (and b-ref (app getb b)))
     ;; Block checks: one let, no assumes, ends with derive
     (define-values (intros assumes lastd) (split-block b 'forall b-ref))
     (define-values (bv bs)
       (match intros
         [(list (intro (list v) s)) (values v s)]
         [(list (intro vs s)) (reject (err:block-intro-multi b-ref))]))
     (define bbody (match lastd [(derive p _) p]))
     (define dprop (prop:forall bv bs bbody))
     (unless (prop=? prop dprop)
       (badr "∀ x ∈ S, P(x)"
             #:more `[" where"
                      (h "  " ,(rich 'pattern "x") " = " ,(rich 'var bv))
                      (h "  " ,(rich 'pattern "P(x)") " = " ,(rich 'prop bbody))]
             #:expect dprop))]
    ;; ----------------------------------------
    [(j:ExistsElim (app getp p) (and b-ref (app getb b)))
     (define-values (pv ps pbody)
       (match p
         [(prop:exists v s body) (values v s body)]
         [_ (bad 1 p "∃ x ∈ S, P(x)")]))
     ;; Block checks: one let, one assume, ends with derive
     (define-values (hintros hassumes lastd) (split-block b 'exists b-ref))
     (define-values (hv hs) (match hintros [(list (intro (list hv) hs)) (values hv hs)]))
     (unless (eq? hs ps)
       (reject `(v (p "The set name in the block's Let statement does not match"
                      "the set name in the quantifier.")
                   (h "In block: " ,(rich 'program-text hs))
                   (h "In quantifier: " ,(rich 'program-text ps)))))
     (define ha (match hassumes [(list (assume ha)) ha]))
     (define hz (match lastd [(derive p _) p]))
     (define body* (prop-subst pbody (list (cons pv (expr:var hv)))))
     (unless (prop=? ha body*)
       (reject
        (err:incorrect-prop
         "The block's assumption" ha "P(y)" null #f
         `[" where"
           (h "  " ,(rich 'pattern "P(x)") " = " ,(rich 'prop pbody))
           (h "  " ,(rich 'pattern "x") " = " ,(rich 'var pv))
           (h "  " ,(rich 'pattern "y") " = " ,(rich 'var hv))]
         body*)))
     (let ([fv (prop-fvs hz (in-scope))])
       (when (memq hv fv)
         (reject
          `(v (p "The rule requires that the last proposition derived in the block"
                 "does not refer to the witness variable.")
              (h "Witness variable: " ,(rich 'var hv))
              (h "Final proposition: " ,(rich 'prop hz))))))
     (unless (prop=? prop hz)
       (badr "q" `((q ,hz)) 'args))]
    [(j:ExistsIntro (app getp p) vm)
     (define-values (rv rs rbody)
       (match prop
         [(prop:exists v s body) (values v s body)]
         [_ (badr "∃ x ∈ S, P(x)")]))
     (when (hash-has-key? (in-scope) rv)
       (reject `(v "Variable chosen for existential quantifier is already in scope."
                   (h "Quantifier variable: " ,(rich 'var rv)))))
     (match vm
       [(list (cons vv ve))
        (unless (equal? vv rv)
          (reject (err:vm-var rv vv)))
        (check-vm-expr ve rs lenv)]
       [_ (reject (err:vm-multi vm))])
     (define body* (prop-subst rbody vm))
     (unless (prop=? p body*)
       (bad 1 p "P(a)"
            #:more `["where (if the rule's result is correct):"
                     (h "  " ,(rich 'pattern "P(x)") " = " ,(rich 'prop rbody))
                     (h "  " ,(rich 'pattern "x") " = " ,(rich 'var rv))
                     (h "  " ,(rich 'pattern "a") " = " ,(rich 'expr (cdar vm)))]
            #:expect body*))]
    ;; ----------------------------------------
    [(j:elim (app getp initp1) vm dir qrefs)
     (define qs (map getp qrefs))
     ;; Part 1: ∀Elim
     (define initp2
       (cond [vm
              (define depth (length vm))
              (define-values (qvars qss body)
                (let loop ([p initp1] [depth depth] [vacc null] [sacc null])
                  (cond [(zero? depth)
                         (values (reverse vacc) (reverse sacc) p)]
                        [else
                         (match p
                           [(prop:forall v s body)
                            (loop body (sub1 depth) (cons v vacc) (cons s sacc))]
                           [_ (reject (err:vm-vars (reverse vacc) (map car vm)))])])))
              (unless (equal? qvars (map car vm))
                (reject (err:vm-vars qvars (map car vm))))
              (for ([vme (in-list (map cdr vm))] [qs (in-list qss)])
                (check-vm-expr vme qs lenv))
              (prop-subst body vm)]
             [else initp1]))
     ;; Part 2: ⇔Elim
     (define initp3
       (cond [dir
              (match initp2
                [(prop:iff pp qq)
                 (case dir
                   [(forward) (prop:implies pp qq)]
                   [(backward) (prop:implies qq pp)])]
                [_ (bad #f initp2 "p ⇔ q")])]
             [else initp2]))
     ;; Part 3: ⇒Elim
     (define result-prop
       (for/fold ([improp initp3]) ([argp (in-list qs)])
         (match improp
           [(prop:implies pp qq)
            #:when (prop=? argp pp)
            qq]
           [_ (bad #f improp "p ⇒ q" `((p ,argp)))])))
     (unless (prop=? prop result-prop)
       (badr #:expect result-prop))]
    [(j:intro (and b-ref (app getb b)))
     ;; Block checks: ends with Derive
     (define-values (intros assumes lastd) (split-block b #f b-ref))
     (define rprop (match lastd [(derive p _) p]))
     (define arprop
       (foldr (lambda (a p)
                (match a
                  [(assume ap) (prop:implies ap p)]))
              rprop
              assumes))
     (define iarprop
       (foldr (lambda (i p)
                (match i
                  [(intro vs s)
                   (foldr (lambda (v p) (prop:forall v s p)) p vs)]))
              arprop
              intros))
     (unless (prop=? prop iarprop)
       (badr #:expect iarprop))]
    ;; ----------------------------------------
    [(j:algebra refs)
     (define ps (map getp refs))
     (for ([p (in-list ps)] [p-ref (in-list refs)])
       (unless (prop-eqn/ineqn? p)
         (reject `(v "Argument to Algebra rule is not an equation or inequality."
                     (h "Argument reference: " ,(rich 'ref p-ref))
                     (h "Argument proposition: " ,(rich 'prop p))))))
     (unless (prop-eqn/ineqn? prop)
       (reject `(v "Derived proposition is not an equation or inequality."
                   (h "Proposition: " ,(rich 'prop prop)))))
     (let ([fvs (prop-fvs prop (in-scope))])
       (when (pair? fvs) (reject (err:prop-fv #f fvs))))
     (check-algebra ps prop)]
    ;; ----------------------------------------
    [(j:ModusTollens (app getp pq) (app getp nq))
     (define-values (p q)
       (match pq
         [(prop:implies p q) (values p q)]
         [_ (bad 1 pq "p ⇒ q")]))
     (unless (prop=? nq (prop:not q))
       (bad 2 nq "¬q" `((p ,p) (q ,q)) 'prev #:expect (prop:not q)))
     (unless (prop=? prop (prop:not p))
       (badr "¬p" `((p ,p) (q ,q)) 'args #:expect (prop:not p)))]
    [(j:DisjSyl (app getp pq) (app getp np))
     (define-values (p q)
       (match pq
         [(prop:or p q) (values p q)]
         [_ (bad 1 pq "p ∨ q")]))
     (cond [(prop=? np (prop:not p))
            (unless (prop=? prop q)
              (badr "q" `((p ,p) (q ,q)) 'args #:expect q))]
           [(prop=? np (prop:not q))
            (unless (prop=? prop p)
              (badr "p" `((p ,p) (q ,q)) 'args #:expect p))]
           [else
            (bad 2 np "¬r" `((p ,p) (q ,q)) 'prev
                 #:more `[(h " where " ,(rich 'pattern "r") " is either "
                             ,(rich 'pattern "p") " or " ,(rich 'pattern "q"))])])]
    [(j:Contradiction (and b-ref (app getb b)))
     ;; Block checks: no lets, one assume, ends with Derive
     (define-values (intros assumes lastd) (split-block b 'contradiction b-ref))
     (define pa (match assumes [(list (assume pa)) pa]))
     (define pz (match lastd [(derive p _) p]))
     (unless (prop-contradiction? pz)
       (reject (err:incorrect-prop
                "The block's final proposition" pz "q ∧ ¬q" null #f
                `["That is, the block must end in a contradiction."] #f)))
     (unless (prop=? prop (prop:not pa))
       (badr "¬p" `((p ,pa)) 'arg #:expect (prop:not pa)))]
    [(j:Repeat (app getp p))
     (unless (prop=? prop p)
       (badr "p" `((p ,p)) 'args #:expect p))]
    ;; ----------------------------------------
    [_ (error 'check-derive "internal error: bad justification: ~e" just)]))

(define (check-vm-expr e s lenv #:env [env (in-scope)])
  ;; Check e has no free vars
  (let ([fvs (expr-fvs e env)])
    (when (pair? fvs) (reject (err:vm-fv fvs))))
  ;; Check e ∈ s
  (cond [(hash-ref lenv s #f)
         => (lambda (elems)
              (unless (expr-in-set-elems? e env elems)
                (reject (err:expr-not-in-set e s))))]
        [else (reject (err:not-declared-set s))]))

(define (check-algebra if-ps then-p)
  (define vars (remove-duplicates (props-fvs (cons then-p if-ps) (hasheq))))
  ;; FIXME: Check every var is Nat -- not needed for current grammar?
  (define (verify venv)
    (when (and (for/and ([if-p (in-list if-ps)])
                 (eval-prop if-p venv))
               (not (eval-prop then-p venv)))
      (reject `(v "The derived proposition is not true."
                  (h "Counter-example: "
                     ,@(add-between
                        (for/list ([(var n) (in-hash venv)])
                          `(h ,(rich 'var var) "=" ,(rich 'expr (expr:integer n))))
                        ", "))))))
  (algebra-run-verifier vars verify))

(define MAX-FUEL #e1e4)
(define MAX-RANDOM #e1e9)
(define NRANDOM #e1e4)

(define (algebra-run-verifier vars verify)
  (define init-fuel (inexact->exact (ceiling (expt MAX-FUEL (/ (max 1 (length vars)))))))
  (define venv (make-hasheq))
  (define (run-with-fuel vars fuel)
    (match vars
      [(list)
       (verify venv)]
      [(list var)
       (hash-set! venv var fuel)
       (verify venv)]
      [(cons var vars)
       (for ([val (in-range 0 fuel)])
         (hash-set! venv var val)
         (run-with-fuel vars (- fuel val)))]))
  (define (run/random vars)
    (match vars
      [(list)
       (verify venv)]
      [(cons var vars)
       (hash-set! venv var (random MAX-RANDOM))
       (run/random vars)]))
  (for ([fuel (in-range init-fuel)])
    (run-with-fuel vars fuel))
  (random-seed 220)
  (for ([iter (in-range NRANDOM)])
    (run/random vars)))

(define (lineno-next n)
  (append (drop-right n 1) (list (add1 (last n)))))

(define (lineno-avail? n at) ;; is #n available at #at
  (define-values (n* at*) (drop-common-prefix n at))
  (match* [n* at*]
    [[(list n1) (cons at1 _)]
     (< n1 at1)]
    [[_ _] #f]))

(define (prop-contradiction? p)
  (match p
    [(prop:and p q)
     (or (prop=? p (prop:not q))
         (prop=? q (prop:not p)))]
    [_ #f]))

;; discard Want lines, split into Let{0,1}, Assume*, Derive
(define (split-block b wantrule b-ref)
  (match b
    [(block rule lines)
     (when (and wantrule (not (equal? rule wantrule)))
       (reject `(v "Wrong kind of block."
                   (h ,(rich 'block-ref b-ref) " declared for " ,(rich 'rule (block-rule-name rule)))
                   (h "Rule used: " ,(rich 'rule (block-rule-name wantrule))))))
     (define (not-want? v) (not (want? v)))
     (define stmts0 (filter not-want? (map line-s lines)))
     (define-values (intros rest1) (splitf-at stmts0 intro?))
     (define-values (assumes rest2) (splitf-at rest1 assume?))
     (values intros assumes (last rest2))]))

;; ============================================================

(define (err:on-line ln [stmt #f])
  `(h "Error on line labeled #" ,(rich 'lineno ln) ":"))

(define (err:in-theorem)
  `(h "Error in Theorem statement."))

(define (err:rule just)
  `(h "Incorrect use of " ,(rich 'rule (justification-rule-name just))))

(define (err:got-arg p)
  `(h "Instead got: " ,(rich 'prop p)))
(define (err:got-result p)
  `(h "Instead found: Derive " ,(rich 'prop p)))

(define (err:prop-fv ref fvs)
  `(v "The proposition refers to one or more variables that are not in scope."
      ,@(if ref `((h "Proposition: " ,(rich 'ref ref))) '())
      (h "Free variables: " ,(rich 'vars fvs))))

(define (err:vm-fv fvs)
  `(v (p "Expressions in the variable mapping refers to one or more variables"
         "that are not in scope.")
      (h "Free variables: " ,(rich 'vars fvs))))

(define (err:witness-fv fvs)
  `(v (p "The witness expression refers to one or more variables"
         "that are not in scope.")
      (h "Free variables: " ,(rich 'vars fvs))))

(define (err:intro-not-fresh var)
  `(v "Let statement introduces a variable that is already in scope."
      (h "Variable: " ,(rich 'var var))))

(define (err:ref-line-unavail ln)
  `(v "The justification refers to a line that is not available."
      (h "Line: " ,(rich 'lineno ln))))

(define (err:ref-axiom-undef ref)
  `(v "The justification refers to an Axiom that is not defined."
      (h "Reference: " ,(rich 'ref ref))))

(define (err:ref-is-block ref)
  `(v (p "The justification requires a reference to a proposition,"
         "but the given line number refers to a block.")
      (h "Reference: " ,(rich 'ref ref))))

(define (err:ref-is-want ref)
  `(v (p "The justification requires a reference to a proposition,"
         "but the given line number refers to a Want statement.")
      (h "Reference: " ,(rich 'ref ref))))

(define (err:ref-is-intro ref)
  `(v (p "The justification requires a reference to a proposition,"
         "but the given line number refers to a Let statement.")
      (h "Reference: " ,(rich 'ref ref))))

(define (err:ref-not-block ref)
  `(v (p "The justification requires a reference to a block.")
      (h "Reference: " ,(rich 'ref ref))))

(define (err:block-ends-with-block ref)
  `(v (p "The given block ends with a nested block.")
      (h "Block: " ,(rich 'block-ref ref))))

(define (err:vm-multi vm)
  `(v (p "The variable mapping contains multiple variables."
         "This rule requires the variable mapping to contain a single variable.")
      (h "Variable mapping's variables: " ,(rich 'vars (map car vm)))))

(define (err:vm-var q-var vm-var)
  `(v "The variable mapping must match the quantifier's variable."
      (h "Quantifier's variable: " ,(rich 'var q-var))
      (h "Variable mapping's variable: " ,(rich 'var vm-var))))

(define (err:vm-vars q-vars vm-vars)
  `(v "The variable mapping must match the quantifier's variables, in order."
      (h "Quantifier's variables: " ,(rich 'vars q-vars))
      (h "Variable mapping's variables: " ,(rich 'vars vm-vars))))

(define (err:block-need-intro ref)
  `(v (p "The rule requires the block to start with a Let statement,"
         "but the given block has no Let statement.")
      (h "Block: " ,(rich 'block-ref ref))))

(define (err:block-intro-multi ref)
  `(v (p "The rule requires the block to start with a Let statement"
         "with a single variable,"
         "but the Let statement contains multiple variables.")
      (h "Block: " ,(rich 'block-ref ref))))

(define (err:block-unwanted-intro ref)
  `(v (p "The rule does not allow the block to have a Let statement,"
         "but the given block starts with a Let statement.")
      (h "Block: " ,(rich 'block-ref ref))))

(define (err:block-need-one-assume ref n-assumes)
  `(v "The rule requires the block to have a single Assume statement,"
      (h "but the referenced block has "
         ,(if (zero? n-assumes) "no" (format "~a" n-assumes))
         " Assume statements.")))

(define (err:block-unwanted-assume ref)
  `(v (p "The rule does not allow the block to contain Assume statements,"
         "but the given block contains at least one Assume statement.")
      (h "Block: " ,(rich 'block-ref ref))))

(define (err:block-need-derive [ref #f])
  `(v (p "The rule requires the given block to end with a Derive statement,"
         "but it does not.")
      (h "Block: " ,(rich 'block-ref ref))))

(define (err:incorrect-prop what got-p form mvenv mvwhy more expected)
  `(v (h ,what ,(if form " does not have the correct form." " is incorrect."))
      ,@(if form `[(h "Required form: " ,(rich 'pattern form))] '())
      ,@(err-part:mvenv mvenv mvwhy)
      ,@more
      ,@(if expected `[(h "Expected: " ,(rich 'prop expected))] '())
      (h "Instead found: " ,(rich 'prop got-p))))

(define (err-part:mvenv mvenv mvwhy)
  (define (explain-why)
    (case mvwhy
      [(arg) " (if the rule's argument is correct)"]
      [(args) " (if the rule's arguments are correct)"]
      [(prev) " (if the rule's previous arguments are correct)"]
      [(res) " (if the rule's result is correct)"]
      [else ""]))
  (cond [(pair? mvenv)
         `[(h " where" ,(explain-why) ":")
           ,@(for/list ([entry (in-list mvenv)])
               (match-define (list mvar prop) entry)
               `(h "  " ,(rich 'pattern (symbol->string mvar))
                   " = " ,(rich 'prop prop)))]]
        [else null]))

(define (err:bad-algebra prop)
  `(v "The result proposition has the wrong form."
      (p "The rule derives either an equation or a proposition with the same"
         "logical structure as the first argument. In the second case, all of"
         "the remaining arguments must be equations.")
      (h "Instead found: " ,(rich 'prop prop))))

(define (err:not-declared-set s)
  `(v "The given identifier is not declared as a set name."
      (h "Identifier: " ,(rich 'program-text (format "~a" s)))))

(define (err:expr-not-in-set e s)
  `(v "The expression does not represent a member of the given set."
      (h "Expression: " ,(rich 'expr e))
      (h "Set name: " ,(rich 'program-text (format "~a" s)))))

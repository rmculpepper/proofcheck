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
         (struct-out proof)
         check-proof)

;; ============================================================

;; LEnv = Hash[LineNo => Statement]

;; check-proof : Proof -> #f or Prop
;; Returns prop for complete proof (ends in Derive), #f otherwise.
(define (check-proof pf)
  (match pf
    [(proof decls lines)
     (define lenv (check-decls decls))
     (check-block lines lenv 'top)
     (match (and (pair? lines) (last lines))
       [(line ln (derive p _)) p]
       [_ #f])]))

(define (check-decls decls)
  (for/fold ([lenv (hash)]) ([decl (in-list decls)])
    (match decl
      [(axiom n p)
       (let ([fvs (prop-fvs p null)])
         (unless (null? fvs)
           (reject (err:prop-fv (ref:axiom n) fvs))))
       (hash-set lenv (ref:axiom n) p)])))

(define (check-block lines lenv b-rule)
  (check-lines lines lenv (block-rule->state b-rule) b-rule))

(define (check-lines lines lenv state b-rule)
  (match lines
    [(list)
     (void)]
    [(cons (line n stmt) lines)
     (define state*
       (parameterize ((error-info (list (err:line n stmt))))
         (check-statement n stmt lenv state b-rule)))
     (check-lines lines (hash-set lenv n stmt) state* b-rule)]))

;; check-statement : LineNo Statement LEnv BlockState BlockRule -> BlockState
;; Returns list of special statement types allowed *after* this statement.
(define (check-statement n stmt lenv state b-rule)
  (match stmt
    [(derive prop just)
     (begin0 (block-state-check/advance state b-rule 'derive)
       (check-derive n prop just lenv))]
    [(want prop)
     (let ([fvs (prop-fvs prop (in-scope))])
       (unless (null? fvs)
         (reject (err:prop-fv #f fvs))))
     state]
    [(assume prop)
     (begin0 (block-state-check/advance state b-rule 'assume)
       (let ([fvs (prop-fvs prop (in-scope))])
         (unless (null? fvs)
           (reject (err:prop-fv #f fvs)))))] 
    [(intro vars s)
     (begin0 (block-state-check/advance state b-rule 'intro)
       (for ([var (in-list vars)])
         (when (memq var (in-scope))
           (reject (err:intro-not-fresh var))))
       (in-scope (append vars (in-scope))))]
    [(block rule lines)
     (begin0 (block-state-check/advance state b-rule 'block)
       (parameterize ((in-scope (in-scope))) ;; mutated by Intro
         ;; Don't check how block ends, because that would interfere with
         ;; (or at least complicate) checking partial proofs.
         (check-block lines lenv rule)))]))

(define (block-rule->state rule)
  (case rule
    [(forall) 'i-d*]
    [(exists) 'i-a-d*]
    [(implies) 'a-d*]
    [(contradiction) 'a-d*]
    [(top) 'd*]
    [(#f) 'i/a-a*-d*]))

;; BlockRule = #f | 'forall | 'exists | 'implies | 'contradiction
;; BlockState = (cons BlockRE BlockRule)
;; BlockRE =
;; - 'i/a-a*-d*
;; - 'i-a-d*
;; - 'i-d*
;; - 'a-d*
;; - 'a*-d*
;; - 'd*

(define (block-state-check/advance state b-rule stype)
  (match stype
    ['intro
     (define not-allowed "Let statement is not allowed here.")
     (match state
       ['i/a-a*-d* 'a*-d*]
       ['i-a-d* 'a-d*]
       ['i-d* 'd*]
       [_ (reject `(v ,not-allowed
                      ,@(err:block-misplaced 'intro state b-rule)
                      ,@(err:block-wanted state b-rule)))])]
    ['assume
     (define not-allowed "Assume statement is not allowed here.")
     (match state
       ['i/a-a*-d* 'a*-d*]
       ['a-d* 'd*]
       ['a*-d* 'a*-d*]
       [_ (reject `(v ,not-allowed
                      ,@(err:block-misplaced 'assume state b-rule)
                      ,@(err:block-wanted state b-rule)))])]
    [(or 'block 'derive)
     (define not-allowed
       (case stype
         [(block) "Block statement is not allowed here."]
         [(derive) "Derive statement is not allowed here."]))
     (match state
       [(or 'a*-d* 'd*) 'd*]
       [_ (reject `(v ,not-allowed
                      ,@(err:block-misplaced stype state b-rule)
                      ,@(err:block-wanted state b-rule)))])]
    ))

(define (block-state->rule state)
  (match state
    ['forall "∀Intro"]
    ['exists "∃Elim"]
    ['implies "⇒Intro"]
    ['contradiction "Contradiction"]))

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
     (list `(p "A block for " ,(rich 'rule (block-state->rule b-rule))
               " should have a Let statement here."))]
    ['a-d*
     (list `(p "A block for " ,(rich 'rule (block-state->rule b-rule))
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
         [_ (error* "internal error: bad proposition reference")])]))
  (define (getb r)
    (match r
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
    [(j:AndElimL (app getp pq))
     (match pq
       [(prop:and pp qq)
        (unless (prop=? prop pp)
          (badr "p" `((p ,pp) (q ,qq)) 'arg #:expect pp))]
       [_ (bad 1 pq "p ∧ q")])]
    [(j:AndElimR (app getp pq))
     (match pq
       [(prop:and pp qq)
        (unless (prop=? prop qq)
          (badr "q" `((p ,pp) (q ,qq)) 'arg #:expect qq))]
       [_ (bad 1 pq "p ∧ q")])]
    [(j:AndIntro (app getp p) (app getp q))
     (define dprop (prop:and p q))
     (unless (prop=? prop dprop)
       (badr "p ∧ q" `((p ,p) (q ,q)) 'args #:expect dprop))]
    [(j:OrElim (app getp pq) (app getp hp) (app getp hq))
     (define-values (p q)
       (match pq
         [(prop:or p q) (values p q)]
         [_ (bad 1 pq "p ∨ q")]))
     (define r
       (match hp
         [(prop:implies pp r)
          #:when (prop=? pp p)
          r]
         [_ (bad 2 hp "p ⇒ r" `((p ,p) (q ,q)) 'prev)]))
     (match hq
       [(prop:implies qq rr)
        #:when (and (prop=? qq q) (prop=? rr r))
        (void)]
       [_ (bad 3 hq "q ⇒ r" `((p ,p) (q ,q) (r ,r)) 'prev)])
     (unless (prop=? prop r)
       (badr "r" `((p ,p) (q ,q) (r ,r)) 'args #:expect r))]
    [(j:OrIntroL (app getp p))
     (match prop
       [(prop:or pp qq)
        #:when (prop=? pp p)
        (void)]
       [_ (badr "p ∨ q" `((p ,p)) 'arg)])]
    [(j:OrIntroR (app getp q))
     (match prop
       [(prop:or pp qq)
        #:when (prop=? qq q)
        (void)]
       [_ (badr "p ∨ q" `((q ,q)) 'arg)])]
    [(j:ImpElim (app getp pq) (app getp p))
     (define-values (pp qq)
       (match pq
         [(prop:implies pp qq)
          (values pp qq)]
         [_ (bad 1 pq "p ⇒ q")]))
     (unless (prop=? pp p)
       (bad 2 p "p" `((p ,pp) (q ,qq)) 'prev #:expect pp))
     (unless (prop=? prop qq)
       (badr "q" `((p ,pp) (q ,qq)) 'args #:expect qq))]
    [(j:ImpIntro (and b-ref (app getb b)))
     (define-values (intros assumes rest) (split-block b))
     (unless (null? intros)
       (reject (err:block-unwanted-intro b-ref)))
     (define pa
       (match assumes
         [(list (assume pa)) pa]
         [_ (reject (err:block-need-one-assume b-ref (length assumes)))]))
     (define plast
       (match (and (pair? rest) (last rest))
         [(derive p _) p]
         [(block _ _) (reject (err:block-ends-with-block b-ref))]
         [#f pa]))
     (define dprop (prop:implies pa plast))
     (unless (prop=? prop dprop)
       (badr "p ⇒ q" `((p ,pa) (q ,plast)) 'arg #:expect dprop))]
    [(j:IffElimF (app getp pq))
     (match pq
       [(prop:iff p q)
        (define dprop (prop:implies p q))
        (unless (prop=? prop dprop)
          (badr "p ⇒ q" `((p ,p) (q ,q)) 'arg #:expect dprop))]
       [_ (bad 1 pq "p ⇔ q")])]
    [(j:IffElimB (app getp pq))
     (match pq
       [(prop:iff p q)
        (define dprop (prop:implies q p))
        (unless (prop=? prop dprop)
          (badr "q ⇒ p" `((p ,p) (q ,q)) 'arg #:expect dprop))]
       [_ (bad 1 pq "p ⇔ q")])]
    [(j:IffIntro (app getp f) (app getp b))
     (match prop
       [(prop:iff p q)
        (unless (prop=? f (prop:implies p q))
          (bad 1 f "p ⇒ q" `((p ,p) (q ,q)) 'res #:expect (prop:implies p q)))
        (unless (prop=? b (prop:implies q p))
          (bad 2 b "q ⇒ p" `((p ,p) (q ,q)) 'res #:expect (prop:implies q p)))]
       [_ (badr "p ⇔ q")])]
    [(j:ForallElim (app getp p) vm)
     (define vmlen (length vm))
     (define-values (vs s body)
       (match p
         [(prop:forall vs s body)
          (cond [(< vmlen (length vs))
                 (define-values (vs1 vs2) (split-at vs vmlen))
                 (values vs1 s (prop:forall vs2 s body))]
                [else (values vs s body)])]
         [_ (bad 1 p "∀ x... ∈ S, P(x...)")]))
     (unless (equal? vs (map car vm))
       (reject (err:vm-vars vs (map car vm))))
     (let ([fv (exprs-fvs (map cdr vm) (in-scope))])
       (when (pair? fv)
         (reject (err:vm-fv fv))))
     (define body* (prop-subst body vm))
     (unless (prop=? prop body*)
       (badr "P(a...)"
             #:more `[" where (if the rule's arguments are correct):"
                      (h "  " ,(rich 'pattern "P(x...)") " = " ,(rich 'prop body))
                      (h "  " ,(rich 'pattern "x...") " = " ,(rich 'vars vs))
                      (h "  " ,(rich 'pattern "a...") " = " ,(rich 'exprs (map cdr vm)))]
             #:expect body*))]
    [(j:ForallIntro (and b-ref (app getb b)))
     (define-values (intros assumes rest) (split-block b))
     (define-values (bvs bs)
       (match intros
         [(list (intro vs s)) (values vs s)]
         [_ (reject (err:block-need-intro b-ref))]))
     (unless (null? assumes)
       (reject (err:block-unwanted-assume b-ref)))
     (define bbody
       (match (and (pair? rest) (last rest))
         [(derive p _) p]
         [_ (reject (err:block-need-derive b-ref))]))
     (define dprop (prop:forall bvs bs bbody))
     (unless (prop=? prop dprop)
       (badr "∀ x... ∈ S, P(x...)"
             #:more `[" where"
                      (h "  " ,(rich 'pattern "x...") " = " ,(rich 'vars bvs))
                      (h "  " ,(rich 'pattern "P(x...)") " = " ,(rich 'prop bbody))]
             #:expect dprop))]
    [(j:ExistsElim (app getp p) (and b-ref (app getb b)))
     (define-values (pv ps pbody)
       (match p
         [(prop:exists (cons v vs) s body)
          (values v s (if (pair? vs) (prop:exists vs s body) body))]
         [_ (bad 1 p "∃ x ∈ S, P(x)")]))
     (define-values (hintros hassumes hrest) (split-block b))
     (define hv
       (match hintros
         ;; FIXME: check hs = s ?
         [(list (intro (list hv) hs)) hv]
         [_ (reject (err:block-need-intro b-ref))]))
     (define body* (prop-subst pbody (list (cons pv (expr:var hv)))))
     (match hassumes
       [(list (assume ha))
        (unless (prop=? ha body*)
          (reject
           (err:incorrect-prop
            "The block's assumption" ha "P(y)" null #f
            `[" where"
              (h "  " ,(rich 'pattern "P(x)") " = " ,(rich 'prop pbody))
              (h "  " ,(rich 'pattern "x") " = " ,(rich 'var pv))
              (h "  " ,(rich 'pattern "y") " = " ,(rich 'var hv))]
            body*)))]
       [as (reject (err:block-need-one-assume b-ref (length as)))])
     (define plast
       (match (and (pair? hrest) (last hrest))
         [(derive p _) p]
         [_ (reject (err:block-need-derive b-ref))]))
     (let ([fv (prop-fvs plast (in-scope))])
       (when (memq hv fv)
         (reject
          `(v (p "The rule requires that the last proposition derived in the block"
                 "does not refer to the witness variable.")
              (h "Witness variable: " ,(rich 'var hv))))))
     (unless (prop=? prop plast)
       (badr "q" `((q ,plast)) 'args))]
    [(j:ExistsIntro (app getp p) vm)
     (define-values (rv rs rbody)
       (match prop
         [(prop:exists (cons v vs) s body)
          (values v s (if (pair? vs) (prop:exists vs s body) body))]
         [_ (badr "∃ x ∈ S, P(x)")]))
     (when (memq rv (in-scope))
       (reject `(v "Variable chosen for existential quantifier is already in scope."
                   (h "Quantifier variable: " ,(rich 'var rv)))))
     (match vm
       [(list (cons vv ve))
        #:when (equal? vv rv)
        (void)
        #; ;; should be impossible
        (let ([fv (expr-fvs ve (in-scope))])
          (when (pair? fv)
            (reject (err:witness-fv fv))))]
       [_ (reject (err:vm-vars (list rv) (map car vm)))])
     (define body* (prop-subst rbody vm))
     (unless (prop=? p body*)
       (bad 1 p "P(a)"
            #:more `["where (if the rule's result is correct):"
                     (h "  " ,(rich 'pattern "P(x)") " = " ,(rich 'prop rbody))
                     (h "  " ,(rich 'pattern "x") " = " ,(rich 'var rv))
                     (h "  " ,(rich 'pattern "a") " = " ,(rich 'expr (cdar vm)))]
            #:expect body*))]
    [(j:elim (app getp initp1) vm dir qrefs)
     (define qs (map getp qrefs))
     ;; Part 1: ∀Elim
     (define initp2
       (cond
         [vm ;; FIXME: copiedd from ForallElim
          (define-values (vs s body)
            (match initp1
              [(prop:forall vs s body)
               (values vs s body)]
              [_ (bad 1 initp1 "∀ x... ∈ S, P(x...)")]))
          (unless (equal? vs (map car vm))
            (reject (err:vm-vars vs (map car vm))))
          (let ([fv (exprs-fvs (map cdr vm) (in-scope))])
            (when (pair? fv) (reject (err:vm-fv fv))))
          (prop-subst body vm)]
         [else initp1]))
     ;; Part 2: ⇔Elim
     (define initp3
       (cond
         [dir
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
     (define-values (intros assumes rest) (split-block b))
     (define-values (bvs bs)
       (match intros
         [(list (intro vs s)) (values vs s)]
         [(list) (values #f #f)]))
     (define bbody
       (let ([last-have
              (cond [(pair? rest) (last rest)]
                    [(pair? assumes) (last assumes)]
                    [else #f])])
         (match last-have
           [(derive p _) p]
           [(assume p) p]
           [_ (reject (err:block-ends-with-block b-ref))])))
     (define iiprop
       (foldr (lambda (a p) (prop:implies a p)) bbody
              (map assume-p assumes)))
     (define aiprop
       (if (pair? bvs) (prop:forall bvs bs iiprop) iiprop))
     (unless (prop=? prop aiprop)
       (badr #:expect aiprop))]
    [(j:algebra refs)
     (define ps (map getp refs))
     (let ([fvs (prop-fvs prop (in-scope))])
       (when (pair? fvs) (err:prop-fv #f fvs)))
     (unless (prop-algebra-can-derive? prop)
       (match ps
         [(cons propa (list (? prop:eq?) ...))
          #:when (prop-same-logic? prop propa)
          (void)]
         [_ (reject (err:bad-algebra prop))]))]
    [(j:ModusTollens (app getp pq) (app getp nq))
     (define-values (pp qq)
       (match pq
         [(prop:implies pp qq)
          (values pp qq)]
         [_ (bad 1 pq "p ⇒ q")]))
     (unless (prop=? nq (prop:not qq))
       (bad 2 nq "¬q" `((p ,pp) (q ,qq)) 'prev #:expect (prop:not qq)))
     (unless (prop=? prop (prop:not pp))
       (badr "¬p" `((p ,pp) (q ,qq)) 'args #:expect (prop:not pp)))]
    [(j:DisjSyl (app getp pq) (app getp np))
     (define-values (pp qq)
       (match pq
         [(prop:or pp qq)
          (values pp qq)]
         [_ (bad 1 pq "p ∨ q")]))
     (cond [(prop=? np (prop:not pp))
            (unless (prop=? prop qq)
              (badr "q" `((p ,pp) (q ,qq)) 'args #:expect qq))]
           [(prop=? np (prop:not qq))
            (unless (prop=? prop pp)
              (badr "p" `((p ,pp) (q ,qq)) 'args #:expect pp))]
           [else
            (bad 2 np "¬r" `((p ,pp) (q ,qq)) 'prev
                 #:more `[(h " where " ,(rich 'pattern "r") " is either "
                             ,(rich 'pattern "p") " or " ,(rich 'pattern "q"))])])]
    [(j:Contradiction (and b-ref (app getb b)))
     (define-values (intros assumes rest) (split-block b))
     (unless (null? intros)
       (reject (err:block-unwanted-intro b-ref)))
     (define pa
       (match assumes
         [(list (assume pa)) pa]
         [_ (reject (err:block-need-one-assume b-ref (length assumes)))]))
     (define plast
       (match (and (pair? rest) (last rest))
         [(derive p _) p]
         [_ (reject (err:block-need-derive b-ref))]))
     (unless (prop-contradiction? plast)
       (reject (err:incorrect-prop
                "The block's final proposition" plast "q ∧ ¬q" null #f
                `["That is, the block must end in a contradiction."] #f)))
     (unless (prop=? prop (prop:not pa))
       (badr "¬p" `((p ,pa)) 'arg #:expect (prop:not pa)))]
    [_ (error 'check-derive "internal error: bad justification: ~e" just)]))

(define (lineno-next n)
  (append (drop-right n 1) (list (add1 (last n)))))

(define (lineno-avail? n at) ;; is #n available at #at
  (define-values (n* at*) (drop-common-prefix n at))
  (match* [n* at*]
    [[(list n1) (cons at1 _)]
     (< n1 at1)]
    [[_ _] #f]))

(define (prop=? p q)
  (equal? p q))

(define (prop-algebra-can-derive? p)
  (match p
    [(prop:not p) (prop-algebra-can-derive? p)]
    [(prop:and p q) (and (prop-algebra-can-derive? p)
                         (prop-algebra-can-derive? q))]
    [(prop:eq _ _) #t]
    [(prop:cmp _ _ _) #t]
    [_ #f]))

(define (prop-same-logic? a b)
  ;; Do the props the same logical structure? (close enough for algebra?)
  (let loop ([a a] [b b])
    (match* [a b]
      [[(prop:not a) (prop:not b)]
       (loop a b)]
      [[(prop:and a1 a2) (prop:and b1 b2)]
       (and (loop a1 b1) (loop a2 b2))]
      [[(prop:or a1 a2) (prop:or b1 b2)]
       (and (loop a1 b1) (loop a2 b2))]
      [[(prop:implies a1 a2) (prop:implies b1 b2)]
       (and (loop a1 b1) (loop a2 b2))]
      [[(prop:iff a1 a2) (prop:iff b1 b2)]
       (and (loop a1 b1) (loop a2 b2))]
      [[(prop:forall avs as ap) (prop:forall bvs bs bp)]
       (and (= (length avs) (length bvs))
            (loop ap bp))]
      [[(prop:exists avs as ap) (prop:exists bvs bs bp)]
       (and (= (length avs) (length bvs))
            (loop ap bp))]
      [[(prop:atomic a) (prop:atomic b)]
       (equal? a b)]
      [[(? prop:eq?) (? prop:eq?)] #t]
      [[(? prop:cmp?) (? prop:cmp?)] #t]
      [[(? prop:pred?) (? prop:pred?)] #t]
      [[(? prop:in?) (? prop:in?)] #t]
      [[_ _] #f])))

(define (prop-contradiction? p)
  (match p
    [(prop:and p q)
     (or (prop=? p (prop:not q))
         (prop=? q (prop:not p)))]
    [_ #f]))

;; discard Want lines, split into Let{0,1}, Assume*, (Block/Derive)*
(define (split-block b)
  (match b
    [(block _ lines)
     (define (not-want? v) (not (want? v)))
     (define stmts0 (filter not-want? (map line-s lines)))
     (define-values (intros rest1) (splitf-at stmts0 intro?))
     (define-values (assumes rest2) (splitf-at rest1 assume?))
     (values intros assumes rest2)]))

;; ============================================================

(define (err:line ln [stmt #f])
  `(h "Error on line labeled #" ,(rich 'lineno ln) ":"))

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

(define (err:ref-not-block ref)
  `(v (p "The justification requires a reference to a block.")
      (h "Reference: " ,(rich 'ref ref))))

(define (err:block-ends-with-block ref)
  `(v (p "The given block ends with a nested block.")
      (h "Block: " ,(rich 'block-ref ref))))

(define (err:vm-vars q-vars vm-vars)
  `(v "The variable mapping must match the quantifier's variables, in order."
      (h "Quantifier's variables: " ,(rich 'vars q-vars))
      (h "Variable mapping's variables: " ,(rich 'vars vm-vars))))

(define (err:block-need-intro ref)
  `(v (p "The rule requires the block to start with a Let statement,"
         "but the given block has no Let statement.")
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

;; Copyright 2024 Ryan Culpepper
;; SPDX-License-Identifier: Apache-2.0

#lang racket/base
(require (for-syntax racket/base)
         racket/list
         racket/match
         racket/string
         parser-tools/yacc
         parser-tools/lex
         (prefix-in : parser-tools/lex-sre))
(provide (all-defined-out))

(define (tokenize get-token)
  (let loop ()
    (define next (get-token))
    (eprintf "~v\n" next)
    (if (eq? next 'EOF) null (cons next (loop)))))

(define (string->tokens lex s)
  (define in (open-input-string s))
  (port-count-lines! in)
  (define (get-token) (lex in))
  (tokenize get-token))

(define-tokens tokens1
  (LINENUMBER
   INTEGER
   IDENTIFIER
   OBJECTNAME
   ))

(define-tokens tokens0
  (EOF
   LP
   RP
   HASH

   DERIVE
   BLOCK
   INTRO
   ASSUME
   WANT
   AXIOM

   NOT
   OR
   AND
   IMPLIES
   IFF
   LEFTARROW
   FORALL
   EXISTS

   ANDINTRO
   ANDELIML
   ANDELIMR
   ORELIM
   ORINTROL
   ORINTROR
   IMPELIM
   IMPINTRO
   IFFELIMF
   IFFELIMB
   IFFINTRO
   FORALLELIM
   FORALLINTRO
   EXISTSELIM
   EXISTSINTRO
   ALGEBRA
   MODUSTOLLENS
   CONTRADICTION

   ORINTRO-is-not-a-rule-name
   IFFELIM-is-not-a-rule-name
   ANDELIM-is-not-a-rule-name

   EQ
   PLUS
   MINUS
   TIMES

   MAPSTO
   COMMA
   COLON
   SEMICOLON
   IN
   BY
   ON
   WITH
   FORWARD
   BACKWARD
   ))

(define-lex-abbrevs
  [$A (:or (:/ "a" "z") (:/ "A" "Z") "_")]
  [$N (:/ "0" "9")]
  [$N+ (:+ $N)]
  [$AN (:or $A $N)]
  [$WS (:or " " "\t" "\v" "\n" "\f" "\r")]
  [$WS+ (:+ $WS)])

(define lex
  (lexer-src-pos
   [(eof) 'EOF]
   [$WS+ (return-without-pos (lex input-port))]
   ["//" (begin (void (read-line input-port))
                (return-without-pos (lex input-port)))]
   [(:: "'" $A (:+ $AN) "'")
    (token-OBJECTNAME (let ([s lexeme]) (substring s 1 (sub1 (string-length s)))))]

   ["(" 'LP]
   [")" 'RP]
   ["#" 'HASH]

   ["Derive" 'DERIVE]
   ["Block" 'BLOCK]
   ["Intro" 'INTRO]
   ["Assume" 'ASSUME]
   ["Want" 'WANT]
   ["Axiom" 'AXIOM]

   ["¬" 'NOT]
   ["∧" 'AND]
   ["∨" 'OR]
   ["⇒" 'IMPLIES]
   ["⇔" 'IFF]
   ["⇐" 'LEFTARROW]
   ["∀" 'FORALL]
   ["∃" 'EXISTS]
   ["not" 'NOT]
   ["and" 'AND]
   ["or"  'OR]
   ["iff" 'IFF]
   ["implies" 'IMPLIES]
   ["forall" 'FORALL]
   ["exists" 'EXISTS]

   ["∧Intro" 'ANDINTRO]
   ["∧ElimL" 'ANDELIML]
   ["∧ElimR" 'ANDELIMR]
   ["∨IntroL" 'ORINTROL]
   ["∨IntroR" 'ORINTROR]
   ["∨Elim"  'ORELIM]
   ["⇒Elim"  'IMPELIM]
   ["⇒Intro" 'IMPINTRO]
   ["⇔ElimF" 'IFFELIMF]
   ["⇔ElimB" 'IFFELIMB]
   ["⇔Intro" 'IFFINTRO]
   ["∀Elim"  'FORALLELIM]
   ["∀Intro" 'FORALLINTRO]
   ["∃Elim"  'EXISTSELIM]
   ["∃Intro" 'EXISTSINTRO]

   ["AndIntro" 'ANDINTRO]
   ["AndElimL" 'ANDELIML]
   ["AndElimR" 'ANDELIMR]
   ["OrIntroL" 'ORINTROL]
   ["OrIntroR" 'ORINTROR]
   ["OrElim"   'ORELIM]
   ["ImpliesElim"  'IMPELIM]
   ["ImpliesIntro" 'IMPINTRO]
   ["ImplicationElim"  'IMPELIM]
   ["ImplicationIntro" 'IMPINTRO]
   ["IffElimF" 'IFFELIMF]
   ["IffElimB" 'IFFELIMB]
   ["IffIntro" 'IFFINTRO]
   ["ForAllElim"  'FORALLELIM]
   ["ForAllIntro" 'FORALLINTRO]
   ["ExistsElim"  'EXISTSELIM]
   ["ExistsIntro" 'EXISTSINTRO]

   ["Algebra" 'ALGEBRA]
   ["ModusTollens" 'MODUSTOLLENS]
   ["Contradiction" 'CONTRADICTION]

   ["∧Elim"   'ANDELIM-is-not-a-rule-name]
   ["∨Intro"  'ORINTRO-is-not-a-rule-name]
   ["⇔Elim"   'IFFELIM-is-not-a-rule-name]
   ["AndElim" 'ANDELIM-is-not-a-rule-name]
   ["OrIntro" 'ORINTRO-is-not-a-rule-name]
   ["IffElim" 'IFFELIM-is-not-a-rule-name]

   ["=" 'EQ]
   ["+" 'PLUS]
   ["-" 'MINUS]
   ["*" 'TIMES]

   ["↦" 'MAPSTO]
   ["," 'COMMA]
   [":" 'COLON]
   [";" 'SEMICOLON]
   ["∈" 'IN]
   ["by" 'BY]
   ["on" 'ON]
   ["with" 'WITH]
   ["forward" 'FORWARD]
   ["fwd" 'FORWARD]
   ["backward" 'BACKWARD]
   ["bwd" 'BACKWARD]

   [":->" 'MAPSTO]
   ["in" 'IN]

   [$N+ (token-INTEGER (string->number lexeme))]
   [(:: $N+ (:+ "." $N+) (:? "."))
    (token-LINENUMBER (map string->number (string-split lexeme "." #:trim? #t)))]
   [(:: $A (:* $AN))
    (token-IDENTIFIER (string->symbol lexeme))]
   ))

(define (base:string->lines s)
  (define in (open-input-string s))
  (port-count-lines! in)
  (base:parse (lambda () (lex in))))

(define (parser-error tok-ok? tok-name tok-value start end #:stack se)
  (error 'parser
         (string-append
          "Unexpected token: ~a~a."
          "\nPosition: ~s:~s to ~s:~s."
          #;"\nParser state = ~v.")
         tok-name
         (if tok-value (format ", ~e" tok-value) "")
         (position-line start) (position-col start)
         (position-line end) (position-col end)
         #;se))

(define base:parse
  (parser
   (tokens tokens0 tokens1)
   (start AxiomsProof)
   (end EOF)
   (error parser-error)
   (src-pos)
   (expected-SR-conflicts 8)

   (precs (left OR)
          (right IMPLIES)
          (nonassoc IFF)
          (left AND)
          (left NOT)

          (right EQ)
          (left PLUS MINUS)
          (left TIMES))
   (grammar

    [AxiomsProof
     [(AxiomDecl AxiomsProof)
      (cons $1 $2)]
     [(Proof) $1]]

    [Proof
     [() null]
     [(Line Proof) (cons $1 $2)]]
    [Line
     [(LineNumber Statement) (line $1 $2)]]

    [AxiomDecl
     [(AXIOM INTEGER COLON Prop)
      (axiom $2 $4)]]

    [LineNumber
     [(INTEGER)
      (list $1)]
     [(LINENUMBER)
      $1]]

    [Statement
     [(DERIVE Prop Justification)
      (derive $2 $3)]
     [(BLOCK)
      'block]
     [(ASSUME Prop)
      (assume $2)]
     [(WANT Prop)
      (want $2)]
     [(INTRO Variable+ IN IDENTIFIER)
      (intro $2 $4)]]

    #;
    [Justification
     [(BY ANDELIML ON PRef) (j:AndElimL $4)]
     [(BY ANDELIMR ON PRef) (j:AndElimR $4)]
     [(BY ANDINTRO ON PRef COMMA PRef) (j:AndIntro $4 $6)]
     [(BY ORELIM ON PRef COMMA PRef COMMA PRef) (j:OrElim $4 $6 $8)]
     [(BY ORINTROL ON PRef) (j:OrIntroL $4)]
     [(BY ORINTROR ON PRef) (j:OrIntroR $4)]
     [(BY IMPELIM ON PRef COMMA PRef) (j:ImpElim $4 $6)]
     [(BY IMPINTRO ON BRef) (j:ImpIntro $4)]
     [(BY IFFELIMF ON PRef) (j:IffElimF $4)]
     [(BY IFFELIMB ON PRef) (j:IffElimB $4)]
     [(BY IFFINTRO ON PRef COMMA PRef) (j:IffIntro $4 $6)]
     [(BY FORALLELIM ON PRef WITH VarMap) (j:ForallElim $4 $6)]
     [(BY FORALLINTRO ON BRef) (j:ForallIntro $4)]
     [(BY EXISTSELIM ON PRef COMMA PRef) (j:ExistsElim $4 $6)]
     [(BY EXISTSINTRO ON PRef WITH VarMap) (j:ExistsIntro $4 $6)]
     [(BY ALGEBRA) (j:algebra null)]
     [(BY ALGEBRA ON PRef+) (j:algebra $4)]
     [(BY PRef SEMICOLON MaybeVarMap MaybeDirection ON PRef+)
      (j:elim $2 $4 $5 $7)]
     [(BY BRef)
      (j:intro $2)]]

    [Justification
     [(BY ANDELIML OnClause) (apply-on "∧ElimL" 1 $3 j:AndElimL)]
     [(BY ANDELIMR OnClause) (apply-on "∧ElimR" 1 $3 j:AndElimR)]
     [(BY ANDINTRO OnClause) (apply-on "∧Intro" 2 $3 j:AndIntro)]
     [(BY ORELIM OnClause)   (apply-on "∨Elim" 3 $3 j:OrElim)]
     [(BY ORINTROL OnClause) (apply-on "∨IntroL" 1 $3 j:OrIntroL)]
     [(BY ORINTROR OnClause) (apply-on "∨IntroR" 1 $3 j:OrIntroR)]
     [(BY IMPELIM OnClause)  (apply-on "⇒Elim" 2 $3 j:ImpElim)]
     [(BY IMPINTRO OnClause) (apply-on "⇒Intro" 1 $3 j:ImpIntro)]
     [(BY IFFELIMF OnClause) (apply-on "⇔ElimF" 1 $3 j:IffElimF)]
     [(BY IFFELIMB OnClause) (apply-on "⇔ElimB" 1 $3 j:IffElimB)]
     [(BY IFFINTRO OnClause) (apply-on "⇔Intro" 2 $3 j:IffIntro)]
     [(BY FORALLELIM ON PRef WITH VarMap) (j:ForallElim $4 $6)]
     [(BY FORALLINTRO ON BRef) (j:ForallIntro $4)]
     [(BY EXISTSELIM ON PRef COMMA PRef) (j:ExistsElim $4 $6)]
     [(BY EXISTSINTRO ON PRef WITH VarMap) (j:ExistsIntro $4 $6)]
     [(BY ALGEBRA) (j:algebra null)]
     [(BY ALGEBRA ON PRef+) (j:algebra $4)]
     [(BY PRef SEMICOLON MaybeVarMap MaybeDirection ON PRef+)
      (j:elim $2 $4 $5 $7)]
     [(BY BRef)
      (j:intro $2)]]

    [MaybeVarMap
     [(WITH VarMap SEMICOLON) $2]
     [() #f]]
    [MaybeDirection
     [(Direction SEMICOLON) $1]
     [() #f]]
    [OnClause
     [(ON PRef+) (cons (cons $n-start-pos $n-end-pos) $2)]]

    [PRef
     [(HASH LineNumber)
      (ref:line $2)]
     [(AXIOM INTEGER)
      (ref:axiom $2)]]
    [BRef
     [(HASH LineNumber)
      (ref:line $2)]]
    [VarMap
     [(Variable+ MAPSTO Expr+)
      (let ([vars $1] [exprs $3])
        (unless (= (length vars) (length exprs))
          (error "bad variable mapping"))
        (map cons vars exprs))]]
    [Direction
     [(FORWARD) 'forward]
     [(IMPLIES) 'forward]
     [(BACKWARD) 'backward]
     [(LEFTARROW) 'backward]]

    [PRef+
     [(PRef) (list $1)]
     [(PRef COMMA PRef+) (cons $1 $3)]]

    [Prop
     [(NOT Prop)
      (prop:not $2)]
     [(Prop AND Prop)
      (prop:and $1 $3)]
     [(Prop OR Prop)
      (prop:or $1 $3)]
     [(Prop IMPLIES Prop)
      (prop:implies $1 $3)]
     [(Prop IFF Prop)
      (prop:iff $1 $3)]
     [(FORALL Variable+ IN Set COMMA Prop)
      (prop:forall $2 $4 $6)]
     [(EXISTS Variable+ IN Set COMMA Prop)
      (prop:exists $2 $4 $6)]
     [(LP Prop RP) $2]

     [(Expr EQ Expr)
      (prop:eq $1 $3)]
     [(IDENTIFIER LP Expr+ RP)
      (prop:pred $1 $3)]
     [(Expr IN Set)
      (prop:in $1 $3)]
     [(IDENTIFIER)
      (prop:atomic $1)]]

    [Expr
     [(INTEGER)
      (expr:integer $1)]
     [(OBJECTNAME)
      (expr:object $1)]
     [(IDENTIFIER)
      (expr:var $1)]
     [(Expr PLUS Expr)
      (expr:plus $1 $3)]
     [(Expr TIMES Expr)
      (expr:times $1 $3)]
     [(IDENTIFIER LP Expr+ RP)
      (expr:apply $1 $3)]]

    [Set
     [(IDENTIFIER) $1]]

    [Variable+
     [(Variable) (list $1)]
     [(Variable COMMA Variable+) (cons $1 $3)]]
    [Variable
     [(IDENTIFIER) $1]]

    [Expr+
     [(Expr) (list $1)]
     [(Expr COMMA Expr+) (cons $1 $3)]]
    )))

(define (apply-on rule n-on on-args0 f . args)
  (match-define (cons srcpair on-args) on-args0)
  (unless (= n-on (length on-args))
    (reject `(v "Justification has the wrong number of proposition arguments after ON."
                (h "Rule: " ,(format "~a" rule))
                (h "Expected: " ,(number->string n-on))
                (h "Instead got: " ,(number->string (length on-args)))
                (h "Source location: " ,(rich 'srcpair srcpair)))))
  (apply f (append args on-args)))

(struct axiom (n p) #:prefab)
(struct line (n s) #:prefab)

(struct derive (p j) #:prefab)
(struct block (ss) #:prefab)
(struct assume (p) #:prefab)
(struct intro (vs s) #:prefab)
(struct want (p) #:prefab)

(struct prop:not (p) #:prefab)
(struct prop:and (p q) #:prefab)
(struct prop:or (p q) #:prefab)
(struct prop:implies (p q) #:prefab)
(struct prop:iff (p q) #:prefab)
(struct prop:forall (vs s p) #:prefab)
(struct prop:exists (vs s p) #:prefab)
(struct prop:atomic (a) #:prefab)

(struct prop:eq (a b) #:prefab)
(struct prop:pred (pred args) #:prefab)
(struct prop:in (e s) #:prefab)

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
      [(prop:forall vs s p) (format "(∀ ~a ∈ ~a, ~a)" (vars->string vs #t) s (loop p))]
      [(prop:exists vs s p) (format "(∃ ~a ∈ ~a, ~a)" (vars->string vs #t) s (loop p))]
      [(prop:atomic a) (format "~a" a)]
      [(prop:eq a b) (format "(~a = ~a)" (expr->string a) (expr->string b))]
      [(prop:pred pred args)
       (format "~a(~a)" pred (string-join (map expr->string args) ", "))]
      [(prop:in e s) (format "(~a ∈ ~a)" (expr->string e) s)]
      [_ (error 'prop->string "internal error: bad prop: ~e" p)])))

(define (expr->string e)
  (match e
    [(expr:integer n) (format "~a" n)]
    [(expr:object s) (format "'~a'" s)]
    [(expr:var var) (format "~a" var)]
    [(expr:plus a b) (format "(~a + ~a)" (expr->string a) (expr->string b))]
    [(expr:times a b) (format "(~a * ~a)" (expr->string a) (expr->string b))]
    [(expr:apply fun args)
     (format "~a(~a)" fun (string-join (map expr->string args) ", "))]
    [_ (format "[EXPR ~e]" e)]))

(define (vars->string vs [tight? #f])
  (string-join (map symbol->string vs) (if tight? "," ", ")))

(define (exprs->string es)
  (string-join (map expr->string es) ", "))

(define (lineno->string ln)
  (string-join (map number->string ln) "."))

(define (prop-subst p vm [vmfv (exprs-fvs (map cdr vm))])
  (let loop ([p p])
    (match p
      [(prop:not p) (prop:not p)]
      [(prop:and p q) (prop:and (loop p) (loop q))]
      [(prop:or p q) (prop:or (loop p) (loop q))]
      [(prop:implies p q) (prop:implies (loop p) (loop q))]
      [(prop:iff p q) (prop:iff (loop p) (loop q))]
      [(prop:forall vs s body)
       (binder-subst prop:forall vs s body vm vmfv)]
      [(prop:exists vs s body)
       (binder-subst prop:exists vs s body vm vmfv)]
      [(prop:atomic a) p]
      [(prop:eq a b) (prop:eq (expr-subst a vm vmfv) (expr-subst b vm vmfv))]
      [(prop:pred pred args)
       (prop:pred pred (for/list ([arg (in-list args)]) (expr-subst arg vm vmfv)))]
      [(prop:in e s) (prop:in (expr-subst e vm vmfv) s)]
      [_ (error 'prop-subst "internal error: bad prop: ~e" p)])))

(define (binder-subst constructor vs s body vm0 vmfv)
  (define vm (filter (lambda (vme) (not (memq (car vme) vs))) vm0))
  (define vs* (map (lambda (v) (if (memq v vmfv) (fresh v) v)) vs))
  (cond [(equal? vs vs*)
         (constructor vs s (prop-subst body vm))]
        [else
         (define vm*
           (for/list ([v (in-list vs)] [v* (in-list vs*)] #:when (not (eq? v v*)))
             (cons v (expr:var v*))))
         (define body* (prop-subst body vm* null))
         (constructor vs* s (prop-subst body* vm))]))

(define (expr-subst e vm vmfv)
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

(define (prop-fvs p [env null])
  (let loop ([p p])
    (match p
      [(prop:not p) (loop p)]
      [(prop:and p q) (append (loop p) (loop q))]
      [(prop:or p q) (append (loop p) (loop q))]
      [(prop:implies p q) (append (loop p) (loop q))]
      [(prop:iff p q) (append (loop p) (loop q))]
      [(prop:forall vs s body) (remove* vs (loop body))]
      [(prop:exists vs s body) (remove* vs (loop body))]
      [(prop:atomic a) null]
      [(prop:eq a b) (append (expr-fvs a env) (expr-fvs b env))]
      [(prop:pred pred args) (exprs-fvs args env)]
      [(prop:in e s) (expr-fvs e env)]
      [_ (error 'prop-fvs "internal error: bad prop: ~e" p)])))

(define (expr-fvs e [env null])
  (let loop ([e e])
    (match e
      [(expr:integer n) null]
      [(expr:object s) null]
      [(expr:var var) (if (memq var env) null (list var))]
      [(expr:plus a b) (append (loop a) (loop b))]
      [(expr:times a b) (append (loop a) (loop b))]
      [(expr:apply fun args) (exprs-fvs args env)])))

(define (exprs-fvs es [env null])
  (append* (for/list ([e (in-list es)]) (expr-fvs e env))))

;; Set by check-proof.
(define all-names (make-parameter (hasheq)))
(define in-scope (make-parameter null))

(define (fresh v)
  (define names (all-names))
  (let loop ([i 1])
    (define vi (string->symbol (format "~a_~a" v i)))
    (cond [(hash-has-key? names vi) (loop (add1 i))]
          [else (all-names (hash-set names vi #t)) vi])))

;; ============================================================

;; pass1 : (Listof Statement) -> (Listof Statement)
;; Collect block lines into block AST.
(define (pass1 lines)
  (match lines
    [(list)
     null]
    [(cons (line n 'block) lines)
     (define (line-number-extends-n? l)
       (match-define (line ln _) l)
       (define-values (n* ln*) (drop-common-prefix n ln))
       (null? n*))
     (define-values (block-lines rest-lines)
       (splitf-at lines line-number-extends-n?))
     (cons (line n (block (pass1 block-lines)))
           (pass1 rest-lines))]
    [(cons l lines)
     (cons l (pass1 lines))]))

;; pass2 : (Listof Statement) -> (Listof Statement)
;; Check line numbers.
(define (pass2 lines [lastn '(0)])
  (match lines
    [(list)
     null]
    [(cons (? axiom? a) lines)
     (cons a (pass2 lines lastn))]
    [(cons (line n stmt) lines)
     (define-values (n* lastn*)
       (drop-common-prefix n lastn))
     (match* [n* lastn*]
       [[(list n0) (list lastn0)]
        #:when (> n0 lastn0)
        (void)]
       [[_ _]
        (reject `(v (h "Bad line number: " ,(rich 'lineno n))
                    (h "Previous line number: " ,(rich 'lineno lastn))))])
     (cons (match stmt
             [(block b-lines)
              (line n (block (pass2 b-lines (append n '(0)))))]
             [_ (line n stmt)])
           (pass2 lines n))]))

;; ============================================================

;; error-info : Parameter of (Listof RichText)
(define error-info (make-parameter null))

(define current-reject
  (make-parameter
   (lambda (rt) (raise-user-error (rich-text->string rt)))))

(define (error* fmt . args)
  (define info (error-info))
  (define msg (apply format fmt args))
  (reject0 (cons 'v+ (append (reverse (error-info)) (list msg)))))

(define (reject . rts)
  (reject0 (cons 'v+ (append (reverse (error-info)) rts))))

(define (reject0 rt) ((current-reject) rt))

;; A RichText is one of
;; - String
;; - (rich Symbol Any)
;; - (cons RichTextType (Listof RichText))
;; where RichTextType is 'v+ | 'v | 'h | 'p
(struct rich (type thing) #:prefab)

(define (rich-text->string rt)
  (match rt
    [(? string? s) s]
    [(? rich? r) (rich->string r)]
    [(cons 'v+ rts) (string-join (map rich-text->string rts) "\n")]
    [(cons 'v rts) (string-join (map rich-text->string rts) "\n")]
    [(cons 'h rts) (string-join (map rich-text->string rts) "")]
    [(cons 'p rts) (string-join (map rich-text->string rts) "\n")]))

(define (rich->string r)
  (match r
    [(rich 'lineno ln) (lineno->string ln)]
    [(rich 'prop p) (prop->string p)]
    [(rich 'expr e) (expr->string e)]
    [(rich 'exprs es) (string-join (map expr->string es) ", ")]
    [(rich 'ref (ref:axiom n)) (format "Axiom ~a" n)]
    [(rich 'ref (ref:line ln)) (format "Proposition #~a" (lineno->string ln))]
    [(rich 'ref #f) "Proposition"]
    [(rich 'var var) (symbol->string var)]
    [(rich 'vars vs) (string-join (map symbol->string vs) ", ")]
    [(rich 'pattern s) s]))

(define (err:line ln [stmt #f])
  `(h "Error on line #" ,(rich 'lineno ln) ":"))

(define (err:rule just)
  `(h "Incorrect use of " ,(justification-rule-name just)))

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

(define (err:misplaced-assume)
  `(v "Assume statement is not allowed here."
      (p "An Assume statement must be at the beginning of the block,"
         "after the Intro statement, if any, but before any"
         "Derive or Block statement.")))

(define (err:misplaced-intro)
  `(v "Intro statement is not allowed here."
      "An Intro statement must be the first statement of a block."))

(define (err:intro-not-fresh var)
  `(v "Intro statement introduces a variable that is already in scope."
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
  `(v (p "The rule requires the block to start with an Intro statement,"
         "but the given block has no Intro statement.")
      (h "Block: " ,(rich 'block-ref ref))))

(define (err:block-unwanted-intro ref)
  `(v (p "The rule does not allow the block to have an Intro statement,"
         "but the given block starts with an Intro statement.")
      (h "Block: " ,(rich 'block-ref ref))))

(define (err:block-need-one-assume ref n-assumes)
  `(v "The rule requires the block to have a single Assume statement,"
      (h "but the referenced block has "
         (if (zero? n-assumes) "no" (format "~a" n-assumes))
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

;; ============================================================

;; Proof = (Listof Statement)

;; string->proof : String -> Proof
(define (string->proof s)
  (define lines1 (base:string->lines s))
  (define lines2 (pass1 lines1))
  (pass2 lines2))

;; LEnv = Hash[LineNo => Statement]

;; check-proof : Lines -> Void
(define (check-proof lines)
  (check-block lines (hash)))

(define (check-block lines lenv)
  (check-lines lines lenv '(intro assume)))

(define (check-lines lines lenv allow)
  (match lines
    [(list)
     (void)]
    [(cons (axiom n p) lines)
     (let ([fvs (prop-fvs p null)])
       (unless (null? fvs)
         (reject (err:prop-fv (ref:axiom n) fvs))))
     (check-lines lines (hash-set lenv (ref:axiom n) p) allow)]
    [(cons (line n stmt) lines)
     (define allow*
       (parameterize ((error-info (list (err:line n stmt))))
         (check-statement n stmt lenv allow)))
     (check-lines lines (hash-set lenv n stmt) allow*)]))

;; STType = (U 'intro 'assume)

;; check-statement : LineNo Statement LEnv (Listof STType) -> (Listof STType)
;; Returns list of special statement types allowed *after* this statement.
(define (check-statement n stmt lenv allow)
  (match stmt
    [(derive prop just)
     (check-derive n prop just lenv)
     null]
    [(want prop)
     allow]
    [(assume prop)
     (unless (memq 'assume allow)
       (reject (err:misplaced-assume)))
     (let ([fvs (prop-fvs prop (in-scope))])
       (unless (null? fvs)
         (reject (err:prop-fv #f fvs))))
     '(assume)]
    [(intro vars s)
     (unless (memq 'intro allow)
       (reject (err:misplaced-intro)))
     (for ([var (in-list vars)])
       (when (memq var (in-scope))
         (reject (err:intro-not-fresh var))))
     (in-scope (append vars (in-scope)))
     '(assume)]
    [(block lines)
     (parameterize ((in-scope (in-scope))) ;; mutated by Intro
       (check-block lines lenv))
     null]))

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
    [(j:OrIntroL q) "∨IntroR"]
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
    [_ #f]))

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
         [(block _) (reject (err:ref-is-block r))]
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
         [_ (bad 1 pq "(p ⇒ q)")]))
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
         [(block _) (reject (err:block-ends-with-block b-ref))]
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
          (error* (string-append
                   "(FIXME) wrong assumption")))
        (void)]
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
     (cond [(prop:eq? prop)
            (void)]
           [else
            (match ps
              [(cons propa (list (? prop:eq?) ...))
               #:when (prop-same-logic? prop propa)
               (void)]
              [_ (reject (err:bad-algebra prop))])])]
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

(define (prop-same-logic? a b)
  ;; Do the props the same logical structure? (close enough for algebra?)
  (let loop ([a a] [b b])
    (match* [a b]
      [[(prop:not a) (prop:not b)]
       (loop a b)]
      [[(prop:and a1 a2) (prop:and b1 b2)]
       (and (loop a1 b1) (a2 b2))]
      [[(prop:or a1 a2) (prop:or b1 b2)]
       (and (loop a1 b1) (a2 b2))]
      [[(prop:implies a1 a2) (prop:implies b1 b2)]
       (and (loop a1 b1) (a2 b2))]
      [[(prop:iff a1 a2) (prop:iff b1 b2)]
       (and (loop a1 b1) (a2 b2))]
      [[(prop:forall avs as ap) (prop:forall bvs bs bp)]
       (and (= (length avs) (length bvs))
            (loop ap bp))]
      [[(prop:exists avs as ap) (prop:exists bvs bs bp)]
       (and (= (length avs) (length bvs))
            (loop ap bp))]
      [[(prop:atomic a) (prop:atomic b)]
       (equal? a b)]
      [[(? prop:eq?) (? prop:eq?)] #t]
      [[(? prop:pred?) (? prop:pred?)] #t]
      [[(? prop:in?) (? prop:in?)] #t]
      [[_ _] #f])))

;; discard Want lines, split into Intro{0,1}, Assume*, (Block/Derive)*
(define (split-block b)
  (match b
    [(block lines)
     (define (not-want? v) (not (want? v)))
     (define stmts0 (filter not-want? (map line-s lines)))
     (define-values (intros rest1) (splitf-at stmts0 intro?))
     (define-values (assumes rest2) (splitf-at rest1 assume?))
     (values intros assumes rest2)]))

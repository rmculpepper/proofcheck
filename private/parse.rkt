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
         "ast.rkt"
         "error.rkt")
(provide (all-defined-out))

(define-tokens tokens1
  (LINENUMBER
   INTEGER
   IDENTIFIER
   VARIABLE
   OBJECTNAME
   ))

(define-empty-tokens tokens0
  (EOF
   End-of-Proposition
   End-of-Justification
   NEWLINE
   LEFTPAREN
   RIGHTPAREN
   LEFTBRACE
   RIGHTBRACE
   ELLIPSES
   HASH
   QED

   DERIVE
   BLOCK
   LET
   ASSUME
   WANT
   AXIOM
   DECLARE
   THEOREM

   NOT
   OR
   AND
   IMPLIES
   IFF
   LEFTARROW
   FORALL
   EXISTS

   INTRO
   ELIM
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
   DISJSYLLOGISM
   CONTRADICTION
   REPEAT

   ORINTRO-is-not-a-rule-name
   IFFELIM-is-not-a-rule-name
   ANDELIM-is-not-a-rule-name

   EQ
   LT
   GT
   LE
   GE

   PLUS
   MINUS
   TIMES

   GETS
   COMMA
   COLON
   SEMICOLON
   IN
   BY
   ON
   FOR
   WITH
   FORWARD
   BACKWARD
   ))

(define-lex-abbrevs
  [$A (:or (:/ "a" "z") (:/ "A" "Z") "_")]
  [$N (:/ "0" "9")]
  [$N+ (:+ $N)]
  [$AN (:or $A $N)]
  [$LWS (:or " " "\t")]
  [$LWS+ (:+ $LWS)]
  [$NL (:or "\v" "\n" "\f" "\r")]
  [$NL+ (:+ $NL)]
  [$WS (:or " " "\t" "\v" "\n" "\f" "\r")]
  [$WS+ (:+ $WS)])

(define ((misspelled alts) word start end)
  (reject `(v "Bad token. Perhaps you misspelled one of the following rule names."
              (h "Invalid word: " ,(rich 'program-text word))
              (h "Suggestions: "
                 ,@(add-between (for/list ([alt alts]) (rich 'program-text alt)) ", "))
              (h "Position: " ,(rich 'srcpair (cons start end))))))

(define reserved-words
  (hash "Derive"  'DERIVE
        "Block"   'BLOCK
        "Let"     'LET
        "Assume"  'ASSUME
        "Want"    'WANT
        "Axiom"   'AXIOM
        "Declare" 'DECLARE
        "Theorem" 'THEOREM
        "QED"     'QED

        "not"     'NOT
        "and"     'AND
        "or"      'OR
        "iff"     'IFF
        "implies" 'IMPLIES
        "forall"  'FORALL
        "exists"  'EXISTS

        "by"        'BY
        "on"        'ON
        "with"      'WITH
        "in"        'IN
        "for"       'FOR
        "forward"   'FORWARD
        "backward"  'BACKWARD
   
        "Intro"    'INTRO
        "Elim"     'ELIM
        "AndIntro" 'ANDINTRO
        "AndElimL" 'ANDELIML
        "AndElimR" 'ANDELIMR
        "OrIntroL" 'ORINTROL
        "OrIntroR" 'ORINTROR
        "OrElim"   'ORELIM
        "IffElimF" 'IFFELIMF
        "IffElimB" 'IFFELIMB
        "IffIntro" 'IFFINTRO
        "ImpliesElim"       'IMPELIM
        "ImpliesIntro"      'IMPINTRO
        "ImplicationElim"   'IMPELIM
        "ImplicationIntro"  'IMPINTRO
        "ForAllElim"        'FORALLELIM
        "ForAllIntro"       'FORALLINTRO
        "ExistsElim"        'EXISTSELIM
        "ExistsIntro"       'EXISTSINTRO
        "Repeat"            'REPEAT
        "Algebra"           'ALGEBRA
        "ModusTollens"      'MODUSTOLLENS
        "Contradiction"     'CONTRADICTION
        "DisjunctiveSyllogism" 'DISJSYLLOGISM

        "AndElim" (misspelled '("AndElimL" "AndElimR"))
        "OrIntro" (misspelled '("OrIntroL" "OrIntroR"))
        "IffElim" (misspelled '("IffElimF" "IffElimB"))

        "ConjElim" (misspelled '("AndElimL" "AndElimR"))
        "ConjElimL" (misspelled '("AndElimL"))
        "ConjElimR" (misspelled '("AndElimR"))
        "ConjIntro" (misspelled '("AndIntro"))

        "DisjIntro" (misspelled '("OrIntroL" "OrIntroR"))
        "DisjIntroL" (misspelled '("OrIntroL"))
        "DisjIntroR" (misspelled '("OrIntroR"))
        "DisjElim" (misspelled '("OrElim"))
        ))

(define lex
  (lexer-src-pos
   [(eof) 'EOF]
   [$LWS+ (return-without-pos (lex input-port))]
   [$NL+ 'NEWLINE]
   [(:: "//" (:* (:~ $NL))) (return-without-pos (lex input-port))]
   #;["//" (begin (void (read-line input-port)) 'NEWLINE)]
   [(:: "'" $A (:+ $AN) "'")
    (token-OBJECTNAME (let ([s lexeme]) (substring s 1 (sub1 (string-length s)))))]

   ["(" 'LEFTPAREN]
   [")" 'RIGHTPAREN]
   ["{" 'LEFTBRACE]
   ["}" 'RIGHTBRACE]
   ["#" 'HASH]

   ["¬" 'NOT]
   ["∧" 'AND]
   ["∨" 'OR]
   ["⇒" 'IMPLIES]
   ["⇔" 'IFF]
   ["⇐" 'LEFTARROW]
   ["∀" 'FORALL]
   ["∃" 'EXISTS]

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

   ["∧Elim"   ((misspelled '("AndElimL" "AndElimR")) lexeme start-pos end-pos)]
   ["∨Intro"  ((misspelled '("OrIntroL" "OrIntroR")) lexeme start-pos end-pos)]
   ["⇔Elim"   ((misspelled '("IffElimF" "IffElimB")) lexeme start-pos end-pos)]

   ["=" 'EQ]
   [">" 'GT]
   ["<" 'LT]
   ["≥" 'GE]
   ["≤" 'LE]
   [">=" 'GE]
   ["<=" 'LE]

   ["+" 'PLUS]
   ["-" 'MINUS]
   ["*" 'TIMES]

   [":=" 'GETS]
   ["↦" 'GETS]
   ["," 'COMMA]
   [":" 'COLON]
   [";" 'SEMICOLON]
   ["∈" 'IN]
   ["..." 'ELLIPSES]

   ["NN" (token-IDENTIFIER 'ℕ)]

   [$N+ (token-INTEGER (string->number lexeme))]
   [(:: $N+ (:+ "." $N+) (:? "."))
    (token-LINENUMBER (map string->number (string-split lexeme "." #:trim? #t)))]
   [(:: $A (:* $AN))
    (cond [(hash-ref reserved-words lexeme #f)
           => (lambda (tok) (if (procedure? tok) (tok lexeme start-pos end-pos) tok))]
          [(for/or ([(reserved tok) (in-hash reserved-words)]
                    #:when (string-ci=? lexeme reserved))
             (if (symbol? tok) reserved tok))
           => (lambda (reserved)
                (if (string? reserved)
                    (reject `(v "Bad token. Incorrect capitalization of reserved word."
                                (h "Got: " ,(rich 'program-text lexeme))
                                (h "Expected: " ,(rich 'program-text reserved))
                                (h "Position: " ,(rich 'srcpair (cons start-pos end-pos)))))
                    (reserved start-pos end-pos)))]
          [(char-lower-case? (string-ref lexeme 0))
           (token-VARIABLE (string->symbol lexeme))]
          [else
           (token-IDENTIFIER (string->symbol lexeme))])]
   ))

;; ----------------------------------------

(define-match-expander token
  (lambda (stx)
    (syntax-case stx ()
      [(_ name) #'(? position-token? (app token-name* name))]
      [(_ name value) #'(? position-token? (app token-name* name) (app token-value* value))])))
(define (token-name* tok) (token-name (position-token-token tok)))
(define (token-value* tok) (token-value (position-token-token tok)))

(define (string->tokens s)
  (define in (open-input-string s))
  (port-count-lines! in)
  (let loop ()
    (define next (lex in))
    (if (eq? (token-name* next) 'EOF) (list next) (cons next (loop)))))

(define ((tokens->lex toks))
  (begin0 (car toks)
    (when (pair? (cdr toks)) (set! toks (cdr toks)))))

;; ----------------------------------------

;; tokens->lines : (Listof Token) -> (Listof (Listof Token))
;; Split on NEWLINE except before BY; retain NEWLINE/EOF.
(define (tokens->lines toks)
  (define (loop toks acc)
    (match toks
      [(list* (token 'NEWLINE) (and toks (list* (token 'BY) _)))
       (loop toks acc)]
      [(list* (and tok (token 'NEWLINE)) toks)
       (values (reverse (cons tok acc)) toks)]
      [(list (and tok (token 'EOF)))
       (values (reverse (cons tok acc)) null)]
      [(list* tok toks)
       (loop toks (cons tok acc))]))
  (cond [(pair? toks)
         (define-values (line toks*) (loop toks null))
         (cons line (tokens->lines toks*))]
        [else null]))

#;
(define (parse-line toks)
  (match toks
    [(list (token 'NEWLINE))
     #f]
    [(list (token 'EOF))
     #f]
    [_ (parse-line* toks)]))

(define (parse-line toks)
  (match toks
    [(list (token name))
     #:when (memq name '(NEWLINE EOF))
     #f]
    [(list* (token name) _)
     #:when (memq name '(AXIOM DECLARE THEOREM QED))
     (parse-line* toks)]
    [(list* (and tok (token 'INTEGER n)) toks)
     (parameterize ((current-lineno (list n)))
       (parse-proof-line tok toks))]
    [(list* (and tok (token 'LINENUMBER ln)) toks)
     (parameterize ((current-lineno ln))
       (parse-proof-line tok toks))]
    [(list* tok _)
     (raise-parser-error* tok
                          `[(p "Expected either a line number or the word "
                               ,(rich 'program-text "Axiom") ".")])]))

(define (parse-proof-line ln-tok toks)
  (match toks
    [(list* (and tok (token 'DERIVE)) toks)
     (parse-derive-line ln-tok tok toks)]
    [(list* (token name) _)
     #:when (memq name '(ASSUME BLOCK LET WANT))
     (parse-line* (cons ln-tok toks))]
    [(list* tok _)
     (raise-parser-error* tok
                          `[(p "Expected a statement keyword, one of"
                               ,(rich 'program-text "Derive") ","
                               ,(rich 'program-text "Block") ","
                               ,(rich 'program-text "Assume") ","
                               ,(rich 'program-text "Let") ", or"
                               ,(rich 'program-text "Want") ".")])]))

(define (make-end name tok)
  (position-token name (position-token-start-pos tok) (position-token-end-pos tok)))

(define (parse-derive-line ln-tok derive-tok toks)
  (define by-index (index-where toks (lambda (tok) (eq? (token-name* tok) 'BY))))
  (cond [by-index
         (define-values (prop-toks just-toks)
           (split-at toks by-index))
         (define ln
           (match ln-tok
             [(token 'INTEGER n) (list n)]
             [(token 'LINENUMBER ln) ln]))
         (define prop
           (let ([end (make-end 'End-of-Proposition (car just-toks))])
             (parse-prop (append prop-toks (list end)))))
         (define just
           (let ([end (make-end 'End-of-Justification (last just-toks))])
             (parse-justification (append (drop-right just-toks 1) (list end)))))
         (line ln (derive prop just))]
        [else
         (define prop (parse-prop toks))
         (raise-parser-error* (last toks)
                              `[(p "Expected" ,(rich 'program-text "by")
                                   "followed by justification.")])]))

(define (parse-line* toks)
  (line-parser (tokens->lex toks)))
(define (parse-prop toks)
  (prop-parser (tokens->lex toks)))

(define (parse-justification toks)
  (match toks
    [(list* (token 'BY) (and tok (token name id)) _)
     #:when (memq name '(IDENTIFIER VARIABLE))
     (raise-parser-error* tok
                          `[(p "Expected rule name after " ,(rich 'program-text "by")
                               " but " ,(rich 'program-text id) " is not the name of a rule.")])]
    [_ (justification-parser (tokens->lex toks))]))

(define (string->prop s)
  (parse-prop (string->tokens s)))

(define current-lineno (make-parameter #f))

(define (err:ln ln)
  (cond [ln `(h "Syntax error on line labeled " ,(rich 'lineno ln))]
        [else `(h "Syntax error")]))

(define (raise-parser-error* tok rts)
  (define t (position-token-token tok))
  (raise-parser-error #t (token-name t) (token-value t)
                      (position-token-start-pos tok) (position-token-end-pos tok)
                      #:rts rts))

(define (raise-parser-error ok? name value start end #:rts [rts null])
  (reject `(v ,(err:ln (current-lineno))
              (h "Unexpected token: "
                 ,(rich 'program-text
                        (cond [(memq name '(EOF NEWLINE End-of-Justification))
                               " "]
                              [else
                               (bytes->string/utf-8
                                (subbytes (current-program-text)
                                          (sub1 (position-offset start))
                                          (sub1 (position-offset end))))]))
                 " ("
                 ,(rich 'token-name name)
                 ;; ,@(if value
                 ;;       `(", " ,(rich 'token-value value))
                 ;;       '())
                 ")")
              (h "Position: "
                 ,(rich 'srcpair (cons start end)))
              ,@(cond [(pair? rts)
                       rts]
                      [(memq name '(EOF NEWLINE))
                       `((p "The line is incomplete."))]
                      [(memq name '(End-of-Proposition))
                       `((p "The" ,(rich 'program-text "Derive")
                            "statement's proposition is incomplete."))]
                      [(memq name '(End-of-Justification))
                       `((p "The" ,(rich 'program-text "Derive")
                            "statement's justification is incomplete."))]
                      [else '()]))))

(match-define (list line-parser
                    prop-parser
                    justification-parser)
  (parser
   (tokens tokens0 tokens1)
   (start Line Prop Justification)
   (end NEWLINE EOF End-of-Proposition End-of-Justification)
   (error raise-parser-error)
   (src-pos)
   #;(debug "proof.grammar")

   (precs (nonassoc COMMA)
          (left OR)
          (right IMPLIES)
          (nonassoc IFF)
          (left AND)
          (left NOT)

          (right EQ LT LE GT GE)
          (left PLUS MINUS)
          (left TIMES))
   (grammar

    [Line
     [(SetDecl) $1]
     [(AxiomDecl) $1]
     [(THEOREM COLON Prop) (setgoal $3)]
     [(QED) (qed)]
     [(ProofLine) $1]]

    [SetDecl
     [(DECLARE IDENTIFIER EQ LEFTBRACE SetElems RIGHTBRACE)
      (setdecl $2 $5)]]
    [SetElems
     [(ELLIPSES) (list (gensym))]
     [(OBJECTNAME) (list $1)]
     [(OBJECTNAME COMMA SetElems) (cons $1 $3)]]

    [AxiomDecl
     [(AXIOM INTEGER COLON Prop)
      (axiom $2 $4)]]

    [ProofLine
     [(LineNumber Statement)
      (line $1 $2)]]

    [LineNumber
     [(INTEGER)
      (list $1)]
     [(LINENUMBER)
      $1]]

    [Statement
     [(DERIVE Prop Justification)
      (derive $2 $3)]
     [(BLOCK BlockFor)
      (block $2 #f)]
     [(ASSUME Prop)
      (assume $2)]
     [(WANT Prop)
      (want $2)]
     [(LET Variable+ IN Set)
      (intro $2 $4)]]

    [BlockFor
     #;[() #f]
     [(FOR INTRO) #f]
     [(FOR FORALLINTRO) 'forall]
     [(FOR IMPINTRO) 'implies]
     [(FOR EXISTSELIM) 'exists]
     [(FOR CONTRADICTION) 'contradiction]]

    [Justification
     [(BY REPEAT OnClause)   (apply-on $3 "Repeat"  j:Repeat '(p))]
     [(BY ANDELIML OnClause) (apply-on $3 "∧ElimL"  j:AndElimL '(p))]
     [(BY ANDELIMR OnClause) (apply-on $3 "∧ElimR"  j:AndElimR '(p))]
     [(BY ANDINTRO OnClause) (apply-on $3 "∧Intro"  j:AndIntro '(p p))]
     [(BY ORELIM OnClause)   (apply-on $3 "∨Elim"   j:OrElim '(p p p))]
     [(BY ORINTROL OnClause) (apply-on $3 "∨IntroL" j:OrIntroL '(p))]
     [(BY ORINTROR OnClause) (apply-on $3 "∨IntroR" j:OrIntroR '(p))]
     [(BY IMPELIM OnClause)  (apply-on $3 "⇒Elim"   j:ImpElim '(p p))]
     [(BY IMPINTRO OnClause) (apply-on $3 "⇒Intro"  j:ImpIntro '(b))]
     [(BY IFFELIMF OnClause) (apply-on $3 "⇔ElimF"  j:IffElimF '(p))]
     [(BY IFFELIMB OnClause) (apply-on $3 "⇔ElimB"  j:IffElimB '(p))]
     [(BY IFFINTRO OnClause) (apply-on $3 "⇔Intro"  j:IffIntro '(p p))]
     [(BY FORALLINTRO OnClause)   (apply-on $3 "∀Intro" j:ForallIntro '(b))]
     [(BY EXISTSELIM OnClause)    (apply-on $3 "∃Elim"  j:ExistsElim '(p b))]
     [(BY MODUSTOLLENS OnClause)  (apply-on $3 "ModusTollens" j:ModusTollens '(p p))]
     [(BY CONTRADICTION OnClause) (apply-on $3 "Contradiction" j:Contradiction '(b))]
     [(BY DISJSYLLOGISM OnClause) (apply-on $3 "DisjunctiveSyllogism" j:DisjSyl '(p p))]
     [(BY ALGEBRA OnClause)  (j:algebra (cdr $3))]
     ;; ----
     [(BY FORALLELIM ON Ref WITH VarMap) (j:ForallElim $4 $6)]
     [(BY EXISTSINTRO ON Ref WITH VarMap) (j:ExistsIntro $4 $6)]
     [(BY ALGEBRA) (j:algebra null)]
     [(BY Ref MaybeVarMap MaybeDirection ON Ref+) (j:elim $2 $3 $4 $6)]
     [(BY INTRO ON Ref) (j:intro $4)]]

    [MaybeVarMap
     [(WITH VarMap) $2]
     [() #f]]
    [MaybeDirection
     [(Direction) $1]
     [() #f]]
    [OnClause
     [(ON Ref+) (cons (cons $n-start-pos $n-end-pos) $2)]]

    [Ref
     [(HASH LineNumber)
      (ref:line $2)]
     [(AXIOM INTEGER)
      (ref:axiom $2)]]
    [VarMap
     [(Variable+ GETS Expr+)
      (let ([vars $1] [exprs $3])
        (unless (= (length vars) (length exprs))
          (reject `(v "Bad variable mapping."
                      "The number of variables does not match the number of expressions."
                      (h "Variables: " ,(rich 'vars vars))
                      (h "Expressions: " ,(rich 'exprs exprs)))))
        (map cons vars exprs))]]
    [Direction
     [(FORWARD) 'forward]
     [(BACKWARD) 'backward]]

    [Ref+
     [(Ref) (list $1)]
     [(Ref COMMA Ref+) (cons $1 $3)]]

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
      (foldr (lambda (v prop) (prop:forall v $4 prop)) $6 $2)]
     [(EXISTS Variable+ IN Set COMMA Prop)
      (foldr (lambda (v prop) (prop:exists v $4 prop)) $6 $2)]
     [(LEFTPAREN Prop RIGHTPAREN) $2]

     [(Expr EQ Expr)
      (prop:cmp 'eq $1 $3)]
     [(Expr GT Expr)
      (prop:cmp 'gt $1 $3)]
     [(Expr LT Expr)
      (prop:cmp 'lt $1 $3)]
     [(Expr GE Expr)
      (prop:cmp 'ge $1 $3)]
     [(Expr LE Expr)
      (prop:cmp 'le $1 $3)]
     [(IDENTIFIER LEFTPAREN Expr+ RIGHTPAREN)
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
     [(VARIABLE)
      (expr:var $1)]
     [(Expr PLUS Expr)
      (expr:plus $1 $3)]
     [(Expr TIMES Expr)
      (expr:times $1 $3)]
     [(VARIABLE LEFTPAREN Expr+ RIGHTPAREN)
      (expr:apply $1 $3)]
     [(LEFTPAREN Expr RIGHTPAREN)
      $2]]

    [Set
     [(VARIABLE) $1]
     [(IDENTIFIER) $1]]

    [Variable+
     [(Variable) (list $1)]
     [(Variable COMMA Variable+) (cons $1 $3)]]
    [Variable
     [(VARIABLE) $1]]

    [Expr+
     [(Expr) (list $1)]
     [(Expr COMMA Expr+) (cons $1 $3)]]
    )))

(define current-program-text (make-parameter #f))

(define (base:string->lines s)
  (parameterize ((current-program-text (string->bytes/utf-8 s)))
    (define toks (string->tokens s))
    (define prelines (tokens->lines toks))
    (filter values (map parse-line prelines))))

;; ----------------------------------------

(define (apply-on on-args0 rulename f argtypes)
  (match-define (cons srcpair on-args) on-args0)
  (unless (= (length argtypes) (length on-args))
    (reject `(v "Justification has the wrong number of arguments after ON."
                (h "Rule: " ,(rich 'rule rulename))
                (h "Expected: " ,(number->string (length argtypes)))
                (h "Instead got: " ,(number->string (length on-args)))
                (h "Source location: " ,(rich 'srcpair srcpair)))))
  (apply f on-args))

;; ============================================================

(struct proof
  (decls ;; (Listof Axiom)
   goal  ;; Prop or #f
   lines ;; (Listof Line)
   qed?  ;; Boolean
   ) #:transparent)

;; string->proof : String -> Proof
(define (string->proof s #:prefix [pre-decls null])
  (define lines1 (base:string->lines s))
  (define lines2 (pass1 lines1))
  (pass2 (append pre-decls lines2)))

;; pass1 : (Listof Statement) -> (Listof Statement)
;; Collect block lines into block AST.
(define (pass1 lines)
  (match lines
    [(list)
     null]
    [(cons (line n (block rule #f)) lines)
     (define (line-number-extends-n? l)
       (match-define (line ln _) l)
       (define-values (n* ln*) (drop-common-prefix n ln))
       (null? n*))
     (define-values (block-lines rest-lines)
       (splitf-at lines line-number-extends-n?))
     (cons (line n (block rule (pass1 block-lines)))
           (pass1 rest-lines))]
    [(cons l lines)
     (cons l (pass1 lines))]))

;; pass2 : (Listof Statement) -> Proof
;; Check line numbers.
(define (pass2 lines)
  (define (wrong v goal?)
    (match v
      [(? axiom? a)
       (reject `(v (h "Axiom declaration not allowed here.")
                   (p "All declarations must come before"
                      "the Theorem statement or the first proof line.")))]
      [(? setdecl? d)
       (reject `(v (h "Set declaration not allowed here.")
                   (p "All declarations must come before"
                      "the Theorem statement or the first proof line.")))]
      [(? setgoal?)
       (reject `(v (h "Theorem statement not allowed here.")
                   ,(if goal?
                        `(p "Only one Theorem statement is allowed.")
                        `(p "The Theorem statement must come before"
                            "the first proof line."))))]
      [(? line?)
       (reject `(v (h "Proof line not allowed here.")
                   (p "All proof lines must come before the QED.")))]))
  (define (axloop lines acc)
    (match lines
      [(cons (? axiom? a) lines)
       (axloop lines (cons a acc))]
      [(cons (? setdecl? d) lines)
       (axloop lines (cons d acc))]
      [lines (values (reverse acc) lines)]))
  (define (thmloop lines)
    (match lines
      [(cons (setgoal goal-prop) lines)
       (values goal-prop lines)]
      [lines (values #f lines)]))
  (define (loop lines lastn goal? acc)
    (match lines
      [(cons (? axiom? a) lines) (wrong a goal?)]
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
       (loop lines n goal?
             (cons (match stmt
                     [(block rule b-lines)
                      (define-values (b-lines* _lines)
                        (loop b-lines (append n '(0)) goal? null))
                      (line n (block rule b-lines*))]
                     [_ (line n stmt)])
                   acc))]
      [lines (values (reverse acc) lines)]))
  (define (qedloop lines goal? qed?)
    (match lines
      [(list) qed?]
      [(list* (qed) lines)
       (unless goal?
         (reject `(v (h "QED not allowed here.")
                     (p "QED is only allowed if there was a Theorem"
                        "declaration before the proof."))))
       (when qed?
         (reject `(v (h "QED not allowed here.")
                     (p "Only one QED is allowed."))))
       (qedloop lines goal? #t)]
      [(list* v lines) (wrong v goal?)]))
  (define-values (decls lines2) (axloop lines null))
  (define-values (goal-prop lines3) (thmloop lines2))
  (define goal? (and goal-prop #t))
  (define-values (proof-lines lines4) (loop lines3 '(0) goal? null))
  (define qed? (qedloop lines4 goal? #f))
  (proof decls goal-prop proof-lines qed?))

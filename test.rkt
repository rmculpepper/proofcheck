#lang racket/base
(require (for-syntax racket/base)
         syntax/location
         syntax/srcloc
         rackunit
         "proof.rkt")
(provide (all-from-out "proof.rkt")
         (all-defined-out))

(define common-axioms (make-parameter null))

(begin-for-syntax
  (define ((tc-macro fun-id) stx)
    (syntax-case stx ()
      [(_ arg ...)
       #`(#,fun-id (quote-srcloc #,stx) arg ...)])))
(define-syntax tok (tc-macro #'tok*))
(define-syntax tperr (tc-macro #'tperr*))
(define-syntax terr (tc-macro #'terr*))

(define (tok* src s)
  (test-case (srcloc->string src)
    (define pf (string->proof s))
    (define result (check-proof (append (common-axioms) pf)))
    (void)))

(define (tperr* src s #:err [pred/rx exn:fail?])
  (test-case (srcloc->string src)
    (check-exn pred/rx (lambda () (string->proof s)))
    (void)))

;; tests for rule violation, not parse errors
(define (terr* src s #:err [pred/rx exn:fail?])
  (test-case (srcloc->string src)
    (define pf (string->proof s))
    (check-exn pred/rx (lambda () (check-proof (append (common-axioms) pf))))
    (void)))

;; ----------------------------------------

(tperr
 #:err #rx"wrong number of arguments"
 "Axiom 1: X and Y \n 1 Derive X by AndElimL on Axiom 1, Axiom 1")

(tperr
 #:err #rx"Bad line number"
 "1 Want A \n 1 Want B")

;; ----------------------------------------
;; check-lines

(terr
 #:err #rx"not in scope"
 "Axiom 1: LE(x,y)")

;; ----------------------------------------
;; check-statement

(terr
 #:err #rx"Block statement is not allowed here"
 "1 Block for ImpliesIntro \n 1.1 Block for Intro \n 1.2 Assume A")

(terr
 #:err #rx"not in scope" ;; Assume
 "1 Block for Intro \n 1.1 Assume LE(x,y)")

(terr
 #:err #rx"Let statement is not allowed here"
 "1 Block for Intro \n 1.1 Assume A \n 1.2 Let x in S")

(terr
 #:err #rx"already in scope" ;; Let
 "1 Block for Intro \n 1.1 Let x in NN \n 1.2 Block for Intro \n 1.2.1 Let x in NN")

(terr
 #:err #rx"within a block"
 "1 Let x in NN")

(terr
 #:err #rx"within a block"
 "1 Assume NN")

(terr
 #:err #rx"not declared as a set name"
 "1 Block for Intro \n 1.1 Let x in A")

;; ----------------------------------------
;; check-derive

(define (badarg) #rx"The rule's.*argument")
(define (badr) #rx"The rule's result")

;; getln
(terr
 #:err #rx"not available"
 "1 Block for Intro \n 1.1 Assume A \n 1.2 Derive A by Repeat on #1.1
  2 Derive A or B by OrIntroL on #1.1")
;; getp
(terr
 #:err #rx"Axiom.*not defined"
 "1 Derive X by AndElimL on Axiom 999")
(terr
 #:err #rx"refers to a Want statement"
 "1 Want A and B \n 2 Derive A by AndElimL on #1")
(terr
 #:err #rx"refers to a block"
 "1 Block for Intro \n 1.1 Assume A \n 1.2 Derive A by Repeat on #1.1
  2 Derive A by AndElimL on #1")
;; getb
(terr
 #:err #rx"requires a reference to a block"
 "1 Want A \n 2 Derive A implies A by ImpliesIntro on #1")

;; And
(tok "Axiom 1: A and B \n 1 Derive A by AndElimL on Axiom 1")
(tok "Axiom 1: A and B \n 1 Derive B by AndElimR on Axiom 1")
(tok "Axiom 1: A \n Axiom 2: B \n 1 Derive A and B by AndIntro on Axiom 1, Axiom 2")
(terr "Axiom 1: A and B \n 1 Derive B by AndElimL on Axiom 1" #:err (badarg))
(terr "Axiom 1: A \n Axiom 2: B \n 1 Derive A by AndIntro on Axiom 1, Axiom 2" #:err (badr))

;; Or
(tok "Axiom 1: A \n 1 Derive A or B by OrIntroL on Axiom 1")
(tok "Axiom 1: A \n 1 Derive B or A by OrIntroR on Axiom 1")
(tok "Axiom 1: A or B \n Axiom 2: A implies C \n Axiom 3: B implies C
1 Derive C by OrElim on Axiom 1, Axiom 2, Axiom 3")
(terr "Axiom 1: A \n 1 Derive B or B by OrIntroL on Axiom 1" #:err (badarg))
(terr "Axiom 1: A \n 1 Derive B or B by OrIntroR on Axiom 1" #:err (badarg))
(terr "Axiom 1: A or B \n Axiom 2: A implies C \n Axiom 3: B implies C
1 Derive C by OrElim on Axiom 1, Axiom 2, Axiom 2" #:err (badarg))
(terr "Axiom 1: A or B \n Axiom 2: A implies C \n Axiom 3: B implies D
1 Derive C by OrElim on Axiom 1, Axiom 2, Axiom 3" #:err (badarg))
(terr "Axiom 1: A or B \n Axiom 2: A implies C \n Axiom 3: B implies C
1 Derive D by OrElim on Axiom 1, Axiom 2, Axiom 3" #:err (badr))

;; Implies
(tok "Axiom 1: A implies B \n Axiom 2: A \n 1 Derive B by ImpliesElim on Axiom 1, Axiom 2")
(tok "1 Block for ImpliesIntro \n 1.1 Assume A \n 1.2 Derive A and A by AndIntro on #1.1, #1.1
2 Derive A implies (A and A) by ImpliesIntro on #1")

(terr "Axiom 1: A \n 1 Derive A by ImpliesElim on Axiom 1, Axiom 1" #:err (badarg))
(terr "Axiom 1: A implies B \n Axiom 2: C \n 1 Derive B by ImpliesElim on Axiom 1, Axiom 2"
      #:err (badarg))
(terr "Axiom 1: A implies B \n Axiom 2: A \n 1 Derive C by ImpliesElim on Axiom 1, Axiom 2"
      #:err (badr))
(terr "1 Block for ImpliesIntro \n 1.1 Let x in NN \n 1.2 Assume A
2 Derive A implies A by ImpliesIntro on #1" #:err #rx"Let statement is not allowed here")
(terr "1 Block for ImpliesIntro
 2 Derive A implies A by ImpliesIntro on #1" #:err #rx"Expected an Assume")
(terr "1 Block for ImpliesIntro \n 1.1 Assume A \n 1.2 Assume B
2 Derive B implies B by ImpliesIntro on #1" #:err #rx"Assume statement is not allowed here")
(terr "1 Block for ImpliesIntro \n 1.1 Assume A \n 1.2 Derive A and A by AndIntro on #1.1, #1.1
2 Derive A implies (A and B) by ImpliesIntro on #1" #:err (badr))
(terr "1 Block for ImpliesIntro \n 1.1 Assume A
1.2 Block for Intro \n 1.2.1 Assume B \n 1.2.2 Derive B by Repeat on #1.2.1
2 Derive A implies A by ImpliesIntro on #1" #:err #rx"must end with a Derive")
(terr "1 Block for ImpliesIntro \n 1.1 Assume A \n 1.2 Derive A and A by AndIntro on #1.1, #1.1
2 Derive A implies B by ImpliesIntro on #1" #:err (badr))
(terr "1 Block for ImpliesIntro \n 1.1 Assume A \n 1.2 Derive A and A by AndIntro on #1.1, #1.1
2 Derive B implies (A and A) by ImpliesIntro on #1" #:err (badr))

;; Iff
(tok "Axiom 1: A iff B \n 1 Derive A implies B by IffElimF on Axiom 1")
(tok "Axiom 1: A iff B \n 1 Derive B implies A by IffElimB on Axiom 1")
(tok "Axiom 1: A implies B \n Axiom 2: B implies A
1 Derive A iff B by IffIntro on Axiom 1, Axiom 2")
(terr "Axiom 1: A iff B \n 1 Derive A implies A by IffElimF on Axiom 1" #:err (badr))
(terr "Axiom 1: A and B \n 1 Derive A implies B by IffElimF on Axiom 1" #:err (badarg))
(terr "Axiom 1: A iff B \n 1 Derive A implies A by IffElimB on Axiom 1" #:err (badr))
(terr "Axiom 1: A and B \n 1 Derive A implies B by IffElimB on Axiom 1" #:err (badarg))
(terr "Axiom 1: A implies C \n Axiom 2: B implies A
1 Derive A iff B by IffIntro on Axiom 1, Axiom 2" #:err (badarg))
(terr "Axiom 1: A implies B \n Axiom 2: C implies A
1 Derive A iff B by IffIntro on Axiom 1, Axiom 2" #:err (badarg))
(terr "Axiom 1: A implies B \n Axiom 2: B implies A
1 Derive A and B by IffIntro on Axiom 1, Axiom 2" #:err (badr))

;; Forall Elim
;(tok "Axiom 1: forall a,b in N, R(a,b)
;1 Derive R(1,2) by ForAllElim on Axiom 1 with a,b := 1,2")
(tok "Axiom 1: forall a,b in NN, R(a,b)
1 Derive forall b in NN, R(1,b) by ForAllElim on Axiom 1 with a := 1")
;(terr "Axiom 1: forall a,b in N, R(a,b)
;1 Derive R(1,2) by ForAllElim on Axiom 1 with x,y := 1,2" #:err #rx"mapping must match")
(terr "Axiom 1: forall a,b in NN, R(a,b)
1 Derive R(1,2) by ForAllElim on Axiom 1 with x := 1" #:err #rx"mapping must match")
(terr "Axiom 1: forall n in NN, R(n)
1 Derive R(x) by ForAllElim on Axiom 1 with n := x" #:err #rx"not in scope")
(terr "Axiom 1: forall n in NN, R(n)
1 Derive R(99) by ForAllElim on Axiom 1 with n := 1" #:err (badr))
;; FIXME: handle one vm for multiple explicit foralls!

;; Forall Intro
(tok "Axiom 102: ∀ x ∈ NN, R(x)
1 Block for ForAllIntro \n 1.1 Let a in NN \n 1.2 Derive R(a) by ForAllElim on Axiom 102 with x := a
2 Derive forall a in NN, R(a) by ForAllIntro on #1")

(terr "1 Block for ForAllIntro \n 1.1 Assume A
2 Derive forall x in NN, A by ForAllIntro on #1" #:err #rx"should have a Let")
(terr "1 Block for ForAllIntro \n 1.1 Let x in NN \n 1.2 Assume A
2 Derive forall x in NN, B by ForAllIntro on #1" #:err #rx"Assume statement is not allowed here")
(terr "1 Block for ForAllIntro \n 1.1 Let x in NN 
1.2 Block for ImpliesIntro \n 1.2.1 Assume A \n 1.2.2 Derive A by Repeat on #1.2.1
2 Derive forall x in NN, A by ForAllIntro on #1" #:err #rx"end with a Derive")
(terr "Axiom 102: ∀ x ∈ NN, R(x)
1 Block for ForAllIntro \n 1.1 Let a in NN \n 1.2 Derive R(a) by ForAllElim on Axiom 102 with x := a
2 Derive forall a in NN, C by ForAllIntro on #1" #:err (badr))

;; Exists Elim
(tok "Axiom 1: exists n in NN, GE(n, 0)
Axiom 2: forall n in NN, GE(n,0) implies Z(0)
1 Block for ExistsElim
  1.1 Let m in NN
  1.2 Assume GE(m, 0)
  1.3 Derive Z(0) by Axiom 2 with n := m on #1.2
2 Derive Z(0) by ExistsElim on Axiom 1, #1")

(terr "Axiom 1: exists n in NN, GE(n, 0)
Axiom 2: forall n in NN, GE(n,0) implies Z(0)
1 Block for ExistsElim
2 Derive Z(0) by ExistsElim on Axiom 1, #1"
      #:err #rx"Expected a Let statement")

(terr "Axiom 1: exists n in NN, GE(n, 0)
Axiom 2: forall n in NN, GE(n,0) implies Z(0)
Axiom 3: A and B
1 Block for ExistsElim
  1.1 Let m in NN
  1.2 Assume Other(m)
  1.3 Derive A by AndElimL on Axiom 3
2 Derive Z(0) by ExistsElim on Axiom 1, #1"
      #:err #rx"assumption") ;; FIXME

(terr "Axiom 1: exists n in NN, GE(n, 0)
Axiom 2: A and B
1 Block for ExistsElim
  1.1 Let m in NN
  1.3 Derive A by AndElimL on Axiom 2
2 Derive A by ExistsElim on Axiom 1, #1"
      #:err #rx"Derive statement is not allowed here")

(terr "Axiom 1: exists n in NN, GE(n, 0)
Axiom 2: forall n in NN, GE(n,0) implies Z(0)
1 Block for ExistsElim
  1.1 Let m in NN
  1.2 Assume GE(m, 0)
  1.3 Derive Z(0) by Axiom 2 with n := m on #1.2
  1.4 Want Blah
2 Derive Z(0) by ExistsElim on Axiom 1, #1"
      #:err #rx"end with a Derive")

(terr "Axiom 1: exists n in NN, GE(n, 0)
Axiom 2: forall n in NN, GE(n,0) implies Z(0)
1 Block for ExistsElim
  1.1 Let m in NN
  1.2 Assume GE(m, 0)
  1.3 Derive GE(m,0) or X by OrIntroL on #1.2
2 Derive GE(m,0) or X by ExistsElim on Axiom 1, #1"
      #:err #rx"not in scope")

(terr "Axiom 1: exists n in NN, GE(n, 0)
Axiom 2: forall n in NN, GE(n,0) implies Z(0)
1 Block for ExistsElim
  1.1 Let m in NN
  1.2 Assume GE(m, 0)
  1.3 Derive Z(0) by Axiom 2 with n := m on #1.2
2 Derive X by ExistsElim on Axiom 1, #1"
      #:err (badr))

;; Exists Intro
(tok "Axiom 1: LE(1,2)
1 Derive exists a in NN, LE(a,2) by ExistsIntro on Axiom 1 with a := 1")

(terr "Axiom 1: LE(1,2) \n 1 Derive A by ExistsIntro on Axiom 1 with a := 1" #:err (badr))
(terr "Axiom 1: LE(1,2) \n 1 Block for Intro \n 1.1 Let a in NN
  1.2 Derive exists a in NN, LE(a,2) by ExistsIntro on Axiom 1 with a := 1"
      #:err #rx"already in scope")
(terr "Axiom 1: LE(1,2)
1 Derive exists a in NN, LE(a,2) by ExistsIntro on Axiom 1 with x := 1"
      #:err #rx"variable mapping")
(terr "Axiom 1: LE(1,2)
1 Derive exists a in NN, LE(a,99) by ExistsIntro on Axiom 1 with a := 1"
      #:err (badarg))

;; Relaxed Elimination
(tok "Axiom 1: forall a,b,c in NN, R(a,b) implies R(b,c) implies R(a,c)
Axiom 2: R(1,2) \n Axiom 3: R(2,3)
1 Derive R(1,3) by Axiom 1 with a,b,c := 1,2,3 on Axiom 2, Axiom 3")

(tok "Axiom 1: forall a,b in NN, LE(a,b) iff GE(b,a)
Axiom 2: LE(1,2)
1 Derive GE(2,1) by Axiom 1 with a,b := 1,2 forward on Axiom 2")

(tok "Axiom 1: forall a,b in NN, LE(a,b) iff GE(b,a)
Axiom 2: GE(2,1)
1 Derive LE(1,2) by Axiom 1 with a,b := 1,2 backward on Axiom 2")

;; FIXME: error tests

;; Relaxed Introduction
(tok "Axiom 1: A and B
1 Block for Intro \n 1.1 Let x,y in NN \n 1.2 Assume LE(x,y) \n 1.3 Derive A by AndElimL on Axiom 1
2 Derive forall x,y in NN, LE(x,y) implies A by Intro on #1")
(tok "Axiom 1: A and B
1 Block for Intro \n 1.1 Assume C \n 1.2 Derive A by AndElimL on Axiom 1
2 Derive C implies A by Intro on #1")
(tok "Axiom 1: A and B
1 Block for Intro \n 1.1 Let x,y in NN \n 1.2 Derive A by AndElimL on Axiom 1
2 Derive forall x,y in NN, A by Intro on #1")

;; FIXME: error tests

;; Algebra
(tok "1 Derive 1+2 = 2+1 by Algebra")
(tok "1 Block for Intro
1.1 Let n in NN
1.2 Derive 2*n = n + n by Algebra")
(tok "1 Block for Intro
1.1 Let a,b in NN
1.2 Assume a < b
1.3 Derive b > a by Algebra on #1.2")

;; ModusTollens
(tok "Axiom 1: A implies B \n Axiom 2: not B
1 Derive not A by ModusTollens on Axiom 1, Axiom 2")

(terr "Axiom 1: A \n Axiom 2: not B
1 Derive not A by ModusTollens on Axiom 1, Axiom 2" #:err (badarg))
(terr "Axiom 1: A implies B \n Axiom 2: not A
1 Derive not B by ModusTollens on Axiom 1, Axiom 2" #:err (badarg))
(terr "Axiom 1: A implies B \n Axiom 2: not B
1 Derive C by ModusTollens on Axiom 1, Axiom 2" #:err (badr))

;; DisjunctiveSyllogism
(tok "Axiom 1: A or B \n Axiom 2: not A
1 Derive B by DisjunctiveSyllogism on Axiom 1, Axiom 2")
(tok "Axiom 1: A or B \n Axiom 2: not B
1 Derive A by DisjunctiveSyllogism on Axiom 1, Axiom 2")

(terr "Axiom 1: A and B \n Axiom 2: not A
1 Derive B by DisjunctiveSyllogism on Axiom 1, Axiom 2" #:err (badarg))
(terr "Axiom 1: A or B \n Axiom 2: A
1 Derive B by DisjunctiveSyllogism on Axiom 1, Axiom 2" #:err (badarg))
(terr "Axiom 1: A or B \n Axiom 2: not A
1 Derive C by DisjunctiveSyllogism on Axiom 1, Axiom 2" #:err (badr))

;; Contradiction
(tok "Axiom 1: not A
1 Block for Contradiction
  1.1 Assume A and B
  1.2 Derive A by AndElimL on #1.1
  1.3 Derive A and not A by AndIntro on #1.2, Axiom 1
2 Derive not(A and B) by Contradiction on #1")

(terr "Axiom 1: not A
1 Block for Contradiction
  1.1 Let x in NN
2 Derive not(A and B) by Contradiction on #1" #:err #rx"Let statement is not allowed here")

(terr "Axiom 1: not A
1 Block for Contradiction
  1.1 Assume A and B
  1.2 Assume C
2 Derive not(A and B) by Contradiction on #1" #:err #rx"Assume statement is not allowed here")

(terr "Axiom 1: not A
1 Block for Contradiction
  1.1 Assume A and B
  1.2 Want Blah
2 Derive not(A and B) by Contradiction on #1" #:err #rx"end with a Derive")

(terr "Axiom 1: not A
1 Block for Contradiction
  1.1 Assume A and B
  1.2 Derive A by AndElimL on #1.1
2 Derive not(A and B) by Contradiction on #1" #:err #rx"end in a contradiction")

(terr "Axiom 1: not A
1 Block for Contradiction
  1.1 Assume A and B
  1.2 Derive A by AndElimL on #1.1
  1.3 Derive A and not A by AndIntro on #1.2, Axiom 1
2 Derive C by Contradiction on #1" #:err (badr))

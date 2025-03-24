;; Copyright 2024-2025 Ryan Culpepper
;; SPDX-License-Identifier: Apache-2.0

#lang racket/base
(require racket/match
         racket/string
         parser-tools/lex
         "ast.rkt")
(provide (all-defined-out))

;; error-info : Parameter of (Listof RichText)
(define error-info (make-parameter null))

;; current-reject : Parameter of (RichText -> None)
(define current-reject
  (make-parameter
   (lambda (rt)
     (raise-user-error (rich-text->string rt)))))

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
    [(rich 'token-name name) (format "~a" name)]
    [(rich 'token-value value) (format "~a" value)]
    [(rich 'program-text value) (format "~a" value)]
    [(rich 'lineno ln) (lineno->string ln)]
    [(rich 'prop p) (prop->string p)]
    [(rich 'expr e) (expr->string e)]
    [(rich 'exprs es) (string-join (map expr->string es) ", ")]
    [(rich 'ref (ref:axiom n)) (format "Axiom ~a" n)]
    [(rich 'ref (ref:line ln)) (format "Proposition #~a" (lineno->string ln))]
    [(rich 'ref #f) "Proposition"]
    [(rich 'block-ref (ref:line ln)) (format "Block #~a" (lineno->string ln))]
    [(rich 'var var) (symbol->string var)]
    [(rich 'vars vs) (string-join (map symbol->string vs) ", ")]
    [(rich 'pattern s) s]
    [(rich 'srcpair p) (let ([a (car p)] [b (cdr p)])
                         (format "~a:~a-~a:~a"
                                 (position-line a) (position-col a)
                                 (position-line b) (position-col b)))]
    [(rich 'rule s) s]))

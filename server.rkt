;; Copyright 2024 Ryan Culpepper
;; SPDX-License-Identifier: Apache-2.0

#lang racket/base
(require racket/runtime-path
         racket/match
         racket/list
         racket/tcp
         web-server/servlet
         web-server/servlet-env
         xml
         json
         "proof.rkt")
(provide (all-defined-out))

(define-runtime-path static-dir "static")
(define headers (list (header #"Access-Control-Allow-Origin" #"*")))

(define (ok-response content-type data)
  (response/output
   #:code 200
   #:mime-type content-type
   #:headers headers
   (lambda (out)
     (cond [(string? data) (write-string data out)]
           [(procedure? data) (data out)]))))

(define-values (dispatch _make-url)
  (dispatch-rules
   [("check")
    #:method "post"
    (lambda (req)
      (define arg (bytes->jsexpr (request-post-data/raw req)))
      (define result (handle-check arg))
      (response/jsexpr result))]
   ))


(define axioms6 (string->proof "
Axiom 1: Small('Mouse')
Axiom 2: Brave('Lion')
Axiom 3: ∀ a,b ∈ A, Fears(a,b) ⇒ ¬Fears(b,a)
Axiom 4: ∀ a,b ∈ A, Small(a) ⇒ Brave(b) ⇒ Fears(a,b)
Axiom 5: ∀ n ∈ NN, Even(n) ⇔ (∃ k ∈ NN, n = 2*k)
Axiom 6: ∀ n ∈ NN, Odd(n) ⇔ (∃ k ∈ NN, n = 2*k + 1)
Axiom 7: ∀ n ∈ NN, Even(n) ∨ Odd(n)
Axiom 8: ∀ d,n ∈ NN, Divides(d,n) ⇔ (∃ k ∈ NN, n = k*d)
Axiom 9: ∀ n ∈ NN, Composite(n) ⇔ (∃ d ∈ NN, (1 < d) ∧ (d < n) ∧ Divides(d, n))
Axiom 10: ∀ n,d,q,r ∈ NN, Div(n,d,q,r) ⇔ (n = q*d + r ∧ (0 < r) ∧ (r < d))
Axiom 11: ∀ n,d,q1,r1,q2,r2 ∈ NN, Div(n,d,q1,r1) ⇒ Div(n,d,q2,r2) ⇒ (q1 = q2) ∧ (r1 = r2)
"))

;; handle-check : JSExpr -> JSExpr
(define (handle-check arg)
  (define proof-text (hash-ref arg 'proof #f))
  (unless proof-text
    (error 'server "no proof included"))
  (let/ec escape
    (parameterize ((current-reject
                    (lambda (rt)
                      (define text (rich-text->string rt))
                      (define html (xexpr->string ((rich-text->xexpr wrap-div) rt)))
                      (escape (hash 'v 1 'format "html" 'error text 'errorh html)))))
      (with-handlers ([exn:fail?
                       (lambda (e)
                         (escape (hash 'v 1 'format "text" 'error (exn-message e))))])
        (define pf (string->proof proof-text))
        (define dprop (check-proof (append axioms6 pf)))
        (define msg
          (cond [dprop
                 `(v "OK."
                     (h "Proven: " ,(rich 'prop dprop)))]
                [else
                 `(p "No errors found, but the proof is incomplete, because"
                     "the main list does not end with a Derive statement.")]))
        (define text (rich-text->string msg))
        (define html (xexpr->string ((rich-text->xexpr wrap-div) msg)))
        (hash 'v 1 'format "html" 'pass text 'passh html)))))

(define ((rich-text->xexpr wrap) rt)
  (match rt
    [(? string? s) (wrap (list s))]
    [(? rich? r) (wrap (list (rich->xexpr r)))]
    [(cons 'v+ rts) (wrap (map (rich-text->xexpr wrap-div) rts))]
    [(cons 'v rts) (wrap (map (rich-text->xexpr wrap-div) rts))]
    [(cons 'h rts) (wrap (map (rich-text->xexpr wrap-span) rts))]
    [(cons 'p rts) (wrap-p (add-between (map (rich-text->xexpr wrap-span) rts) " "))]))

(define (wrap-div xs) `(div ([class "rt_v"]) ,@xs))
(define (wrap-span xs) `(span ([class "rt_h"]) ,@xs))
(define (wrap-p xs) `(div ([class "rt_p par"]) ,@xs))

(define (rich->xexpr r)
  (define (text) (rich->string r))
  (match r
    [(rich 'lineno ln) `(span ([class "r_lineno"]) ,(text))]
    [(rich 'prop p) `(span ([class "r_prop"]) ,(text))]
    [(rich 'expr e) `(span ([class "r_expr"]) ,(text))]
    [(rich 'exprs es) `(span ([class "r_exprs"])
                             ,@(add-between
                                (for/list ([e (in-list es)])
                                  `(span ([class "r_expr"]) ,(expr->string e)))
                                ", "))]
    [(rich 'ref (ref:axiom n))
     `(span ([class "r_ref_ax"]) ,(text))]
    [(rich 'ref (ref:line ln))
     `(span ([class "r_ref_line"]) ,(text))]
    [(rich 'ref #f) `(span ([class "r_ref_prop"]) (text))]
    [(rich 'block-ref (ref:line ln))
     `(span ([class "r_block_line"]) ,(text))]
    [(rich 'var var) `(span ([class "r_var"]) ,(text))]
    [(rich 'vars vs) `(span ([class "r_vars"])
                            ,@(add-between
                               (for/list ([v (in-list vs)])
                                 `(span ([class "r_var"]) ,(symbol->string v)))
                               ", "))]
    [(rich 'pattern s) `(span ([class "r_pattern"]) ,(text))]
    [(rich 'srcpair p) `(span ([class "r_srcpair"]) ,(text))]
    [(rich 'rule s) `(span ([class "r_rule"]) ,(text))]
    [_ `(span ([class "r_unknown"]) ,(text))]))

;; ============================================================

(define (start [log? #f])
  (serve/servlet dispatch
                 #:port 17180
                 #:listen-ip #f ;; all interfaces
                 #:servlet-regexp #rx""
                 #:command-line? #t
                 ;; #:launch-browser? #f
                 #:extra-files-paths (list (path->string static-dir))
                 #:log-file (and log? "log.txt")))

(module+ main
  (start #t))

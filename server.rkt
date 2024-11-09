;; Copyright 2024 Ryan Culpepper
;; SPDX-License-Identifier: Apache-2.0

#lang racket/base
(require racket/runtime-path
         racket/tcp
         web-server/servlet
         web-server/servlet-env
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
                      (escape (hash 'v 1 'format "text" 'error text)))))
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
                 `(p "OK. No errors found, but the proof is incomplete, because"
                     "the main list does not end with a Derive statement.")]))
        (hash 'v 1 'format "text" 'pass (rich-text->string msg))))))

;; ============================================================

(define (start [log? #f])
  (serve/servlet dispatch
                 #:port 17180
                 #:listen-ip #f ;; all interfaces
                 #:servlet-regexp #rx""
                 #:command-line? #t
                 ;; #:launch-browser? #f
                 #:extra-files-paths (list (path->string static-dir))
                 #:log-file (if log? "/dev/stdout" #f)))

(module+ main
  (start #f))

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

(define (ok-response content-type data)
  (response/output
   #:code 200
   #:mime-type content-type
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
      (define pf (string->proof proof-text))
      (check-proof pf)
      (hash 'v 1 'format "text" 'pass "OK"))))

;; ============================================================

(define (start [log? #f])
  (serve/servlet dispatch
                 #:port 17180
                 #:servlet-regexp #rx""
                 #:command-line? #t
                 ;; #:launch-browser? #f
                 #:extra-files-paths (list (path->string static-dir))
                 #:log-file (if log? "/dev/stdout" #f)))

(module+ main
  (start #f))

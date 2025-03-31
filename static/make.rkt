#lang racket/base
(require xml
         racket/runtime-path)

(define-runtime-path here ".")

(define (make-html dir infile outfile)
  (define xe (call-with-input-file* (build-path dir infile) read))
  (call-with-output-file* (build-path dir outfile)
    #:exists 'truncate/replace
    (lambda (out)
      (define xml (xexpr->xml xe))
      (fprintf out "<!DOCTYPE html>\n")
      (fprintf out "<!-- Generated from ~s -->" infile)
      (display-xml/content xml out #:indentation 'none #;'scan))))

(module+ main
  (for ([page '("index" "mini")])
    (printf "Making ~a.html\n" page)
    (make-html here (format "~a.rktd" page) (format "~a.html" page))))

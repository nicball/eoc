#lang racket
(require "utilities.rkt")
(require "interp-Lcast-prime.rkt")
(require "interp-Cvar.rkt")
(require "interp-Cif.rkt")
(require "interp-Cwhile.rkt")
(require "interp-Cvec.rkt")
(require "interp-Cvecof.rkt")
(require "interp-Cfun.rkt")
(require "interp-Clambda.rkt")
(provide interp-Cany-proxy)

(define (interp-Cany-proxy-mixin super-class)
  (class super-class
    (super-new)
    (inherit call-function)
         
    (define/override (apply-fun f args debug)
      (call-function (vector-ref f 0) (cons f args) debug))))

(define Cany-proxy-class
  (interp-Cany-proxy-mixin
   (interp-Clambda-mixin
    (interp-Cfun-mixin
     (interp-Cvecof-mixin
      (interp-Cvec-mixin
       (interp-Cwhile-mixin
        (interp-Cif-mixin
         (interp-Cvar-mixin
          interp-Lcast-prime-class)))))))))

(define (interp-Cany-proxy p)
  (send (new Cany-proxy-class) interp-program p))


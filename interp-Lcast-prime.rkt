#lang racket
(require "interp-Lvec-prime.rkt")
(require "interp-Lfun-prime.rkt")
(require "interp-Llambda-prime.rkt")
(require "interp-Lany-prime.rkt")
(require "interp-Lcast.rkt")
(require "utilities.rkt")
(provide interp-Lcast-prime interp-Lcast-prime-mixin interp-Lcast-prime-class)

(define (interp-Lcast-prime-mixin super-class)
  (class super-class
    (super-new)
         
    (define/override (apply-fun f args debug)
      (if (vector? f)
        (super apply-fun (vector-ref f 0) (cons f args) debug)
        (super apply-fun f args debug)))))

(define interp-Lcast-prime-class
  (interp-Lcast-prime-mixin
   (interp-Lany-prime-mixin
    (interp-Llambda-prime-mixin
     (interp-Lfun-prime-mixin
      (interp-Lvec-prime-mixin
       interp-Lcast-class))))))
    
(define (interp-Lcast-prime p)
  (send (new interp-Lcast-prime-class) interp-program p))


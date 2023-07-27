(define (f [x : (Vector Any)])
  (vector-ref x 0))

(f (vector 42))

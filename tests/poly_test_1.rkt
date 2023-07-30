(: map
  (All (T)
    ((All (U) (U -> Integer))
     (Vector T Integer Boolean)
     ->
     (Vector Integer Integer Integer))))
(define (map f v)
  (vector
    (f (vector-ref v 0))
    (f (vector-ref v 1))
    (f (vector-ref v 2))))

(: f (All (T) (T -> Integer)))
(define (f v) 42)

(let ([v (vector (void) 1 #f)])
  (vector-ref (map f v) 0))

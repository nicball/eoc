(define (map [f : (Integer -> Integer)] [v : (Vector Integer Integer)]) : (Vector Integer Integer)
  (vector
    (f (vector-ref v 0))
    (f (vector-ref v 1))))

(define (inc [x : Any]) : Any
  (+ 1 x))

(let ([v (vector 0 41)])
  (vector-ref
    (map inc v)
    1))

(define (inc [x : Integer]) : Integer
  (+ 1 x))

(define (map [f : (Integer -> Integer)] [vec : (Vector Integer Integer Integer)]) : (Vector Integer Integer Integer)
  (vector
    (f (vector-ref vec 0))
    (f (vector-ref vec 1))
    (f (vector-ref vec 2))))

(let ([v (vector 41 42 43)])
  (vector-ref (map inc v) 0))

(let ([v (vector (vector 1) #f (lambda (x) x) 41)])
  (begin
    (while (vector-ref v 1)
      (read))
    (let ([i 3])
      (+ (vector-ref (vector-ref v 0) 0) ((vector-ref v 2) (vector-ref v i))))))

(define (sum [x : Integer]) : Integer
  (let ([s 0])
    (begin
      (while (> x 0)
        (begin
          (set! s (+ s x))
          (set! x (- x 1))))
      s)))

(- (sum 9) 3)

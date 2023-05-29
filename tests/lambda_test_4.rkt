(define (f [x : Integer]) : Integer
  (let ([g (lambda: () : Integer (begin (set! x (+ x 1)) 0))])
    (let ([h (lambda: () : Integer x)])
      (begin
        (g)
        (h)))))

(f 41)

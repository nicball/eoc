(let ([x 2])
  (+ (+ x (begin (set! x (+ x 18)) x)) x))

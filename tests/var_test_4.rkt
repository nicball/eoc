(let ([x 5])
  (+ x
    (let ([y 6])
      (+ x
       (let ([x 7])
         (+ x y))))))

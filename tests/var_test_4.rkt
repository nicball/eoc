(let ([x 10])
  (+ x
    (let ([y 8])
      (+ x
       (let ([x 14])
         (+ x y))))))

(let ([retval 0])
  (begin
    (let ([constant 40])
      (let ([i 1])
        (while (< i 5)
          (let ([m (+ 2 constant)])
            (begin
              (set! retval m)
              (set! i (+ i 1)))))))
    retval))

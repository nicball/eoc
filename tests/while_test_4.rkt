(let ([r 0])
  (begin
    (let ([x 42])
      (set! r x))
    (let ([x #t])
      (if x
        r
        0))))

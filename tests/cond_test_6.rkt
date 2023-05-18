(let ([x #t])
  (if (if (and x #t) (not #t) #f)
    0
    42))

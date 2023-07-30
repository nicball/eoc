(let ([f1 (lambda: ([x : Integer]) : Integer 42)])
  (let ([f2 (lambda: () : Integer (f1 5))])
    (f2)))

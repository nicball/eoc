(begin
  (let ([x #f])
    (let ([y (while x
                (read))])
      42)))

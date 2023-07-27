(define (some_func [x : Integer] [y : Integer]) : Integer 0)

(if (eq? (procedure-arity some_func) 2)
  42
  0)

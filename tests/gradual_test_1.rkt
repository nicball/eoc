(define (map_inplace [f : (Any -> Any)] [v : (Vector Any Any)]) : Void
  (begin
    (vector-set! v 0 (f (vector-ref v 0)))
    (vector-set! v 1 (f (vector-ref v 1)))))

(define (inc [x : Any]) : Any
  (+ x 1))

(let ([v (vector 0 41)])
  (begin
    (map_inplace inc v)
    (vector-ref v 1)))

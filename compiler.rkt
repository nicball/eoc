#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lint examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following compiler pass is just a silly one that doesn't change
;; anything important, but is nevertheless an example of a pass. It
;; flips the arguments of +. -Jeremy
(define (flip-exp e)
  (match e
    [(Var x) e]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (Prim '- (list (flip-exp e1)))]
    [(Prim '+ (list e1 e2)) (Prim '+ (list (flip-exp e2) (flip-exp e1)))]))

(define (flip-Lint e)
  (match e
    [(Program info e) (Program info (flip-exp e))]))


;; Next we have the partial evaluation pass described in the book.
(define (pe-neg r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [else (Prim '- (list r))]))

(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [(_ _) (Prim '+ (list r1 r2))]))

(define (pe-exp e)
  (match e
    [(Int n) (Int n)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]))

(define (pe-Lint p)
  (match p
    [(Program info e) (Program info (pe-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x)
       (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Let x e body)
       (letrec ([fresh
                 (lambda (cand)
                   (if (dict-has-key? env cand)
                     (fresh (string->symbol (string-append (symbol->string cand) "'")))
                     cand))]
                [new-x (fresh x)])
         (Let new-x ((uniquify-exp env) e) ((uniquify-exp (dict-set env x new-x)) body)))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (define (unzip lst) (foldr (lambda (p acc) (cons (cons (car p) (car acc)) (cons (cdr p) (cdr acc)))) (cons '() '()) lst))
  (define (rco-exp e)
    (match e
      [(Let x e body) (Let x (rco-exp e) (rco-exp body))]
      [(Prim op args)
       (letrec ([bindings-and-atoms (unzip (map rco-atom args))]
                [bindings (apply append (car bindings-and-atoms))]
                [list-to-lets
                 (lambda (lst body)
                   (if (pair? lst)
                     (Let (caar lst) (cdar lst) (list-to-lets (cdr lst) body))
                     body))])
         (list-to-lets bindings (Prim op (cdr bindings-and-atoms))))]
      [_ e]))
  (define (rco-atom e)
    (match e
      [(Let x e body)
       (match (rco-atom body)
         [(cons bindings body) (cons (append (list (cons x (rco-exp e))) bindings) body)])]
      [(Prim op args)
       (letrec ([x (gensym 'tmp)]
             [bindings-and-atoms (unzip (map rco-atom args))]
             [bindings (apply append (car bindings-and-atoms))])
         (cons (append bindings (list (cons x (Prim op (cdr bindings-and-atoms))))) (Var x)))]
      [_ (cons '() e)]))
  (match p
    [(Program info e) (Program info (rco-exp e))]))

;; explicate-control : R1 -> C0
(define (explicate-control p)
  (define (explicate-tail e)
    (match e
      [(Let x e body) (explicate-assign x e (explicate-tail body))]
      [_ (Return e)]))
  (define (explicate-assign x e tail)
    (match e
      [(Let x2 e2 body) (explicate-assign x2 e2 (explicate-assign x body tail))]
      [_ (Seq (Assign (Var x) e) tail)]))
  (match p
    [(Program info e) (CProgram info (list (cons 'start (explicate-tail e))))]))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (error "TODO: code goes here (select-instructions)"))

;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-homes p)
  (error "TODO: code goes here (assign-homes)"))

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (error "TODO: code goes here (patch-instructions)"))

;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
  (error "TODO: code goes here (prelude-and-conclusion)"))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( ("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
     ;; Uncomment the following passes as you finish them.
     ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
     ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
     ;; ("instruction selection" ,select-instructions ,interp-x86-0)
     ;; ("assign homes" ,assign-homes ,interp-x86-0)
     ;; ("patch instructions" ,patch-instructions ,interp-x86-0)
     ;; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))

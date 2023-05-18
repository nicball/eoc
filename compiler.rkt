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
(require "interp.rkt")

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
      [(Let _ _ _)
       (let ([le (gensym 'tmp-let)])
         (cons (list (cons le (rco-exp e))) (Var le)))]
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
  (define (si-atom atom)
    (match atom
      [(Int i) (Imm i)]
      [(Var x) (Var x)]))
  (define (si-stmt s)
    (match s
      [(Assign x (Prim 'read '())) (list (Callq 'read_int 0) (Instr 'movq (list (Reg 'rax) x)))]
      [(Assign x (Prim '- (list a)))
       (if (and (Var? x) (Var? a) (eq? (Var-name x) (Var-name a)))
         (list (Instr 'negq (list a)))
         (list (Instr 'movq (list (si-atom a) x)) (Instr 'negq (list x))))]
      [(Assign x (Prim '- (list a b)))
       (if (and (Var? x) (Var? a) (eq? (Var-name x) (Var-name a)))
         (list (Instr 'subq (list (si-atom b) a)))
         (list (Instr 'movq (list (si-atom a) x)) (Instr 'subq (list (si-atom b) x))))]
      [(Assign x (Prim '+ (list a b)))
       (cond
        [(and (Var? x) (Var? a) (eq? (Var-name x) (Var-name a))) (list (Instr 'addq (list (si-atom b) a)))]
        [(and (Var? x) (Var? b) (eq? (Var-name x) (Var-name b))) (list (Instr 'addq (list (si-atom a) b)))]
        [else (list (Instr 'movq (list (si-atom a) x)) (Instr 'addq (list (si-atom b) x)))])]
      [(Assign x atom) (list (Instr 'movq (list (si-atom atom) x)))]))
  (define (si-tail tail)
    (match tail
      [(Return e) (append (si-stmt (Assign (Reg 'rax) e)) (list (Jmp 'conclusion)))]
      [(Seq stmt tail) (append (si-stmt stmt) (si-tail tail))]))
  (match p
    [(CProgram info blocks)
     (X86Program info (for/list ([b blocks]) (cons (car b) (Block '() (si-tail (cdr b))))))]))

;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-homes p)
  (match p
    [(X86Program info blocks)
     (define locals-types
       (if (dict-has-key? info 'locals-types)
         (dict-ref info 'locals-types)
         '()))
     (define stack-size
       (let* ([ss (* (length locals-types) 8)]
              [rem (remainder ss 16)])
         (if (> rem 0)
           (+ ss (- 16 rem))
           ss)))
     (define (get-locals-offset symbol)
       (define (go lst n)
         (cond
          [(null? lst) (error "get-locals-offset: out of bound")]
          [(eq? (caar lst) symbol) n]
          [else (go (cdr lst) (+ 1 n))]))
       (* -8 (go locals-types 1)))
     (define (ah-arg arg)
       (match arg
         [(Var x) (Deref 'rbp (get-locals-offset x))]
         [_ arg]))
     (define (ah-instr instr)
       (match instr
         [(Instr op args) (Instr op (map ah-arg args))]
         [_ instr]))
     (X86Program (dict-set info 'stack-size stack-size)
       (for/list ([label-and-block blocks])
         (match label-and-block
           [(cons label (Block info instrs))
            (cons label (Block info (map ah-instr instrs)))])))]))

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (define (patch instr)
    (match instr
      [(Instr op (list (Deref reg1 off1) (Deref reg2 off2)))
       (list
         (Instr 'movq (list (Deref reg1 off1) (Reg 'rax)))
         (Instr op (list (Reg 'rax) (Deref reg2 off2))))]
      [_ (list instr)]))
  (match p
    [(X86Program info blocks)
     (X86Program info (for/list ([label-and-block blocks])
       (match label-and-block
         [(cons label (Block info instrs))
          (cons label (Block info (apply append (map patch instrs))))])))]))

;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
  (match p
    [(X86Program info blocks)
     (X86Program info (append blocks (list
       (cons 'main (Block '() (list
         (Instr 'pushq (list (Reg 'rbp)))
         (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))
         (Instr 'subq (list (Imm (dict-ref info 'stack-size)) (Reg 'rsp)))
         (Jmp 'start))))
       (cons 'conclusion (Block '() (list
         (Instr 'addq (list (Imm (dict-ref info 'stack-size)) (Reg 'rsp)))
         (Instr 'popq (list (Reg 'rbp)))
         (Retq)))))))]))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( ("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
     ;; Uncomment the following passes as you finish them.
     ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
     ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
     ("instruction selection" ,select-instructions ,interp-x86-0)
     ("assign homes" ,assign-homes ,interp-x86-0)
     ("patch instructions" ,patch-instructions ,interp-x86-0)
     ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))

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
(require graph)
(require "priority_queue.rkt")

(define (dict-merge a b)
  (for ([p b])
    (set! a (dict-set a (car p) (cdr p))))
  a)

(define (concat lsts) (apply append lsts))

(define (slow-set-count s) (set-count (if (set? s) s (list->set s))))

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
                [bindings (concat (car bindings-and-atoms))]
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
             [bindings (concat (car bindings-and-atoms))])
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

;; uncover-live : x86Var -> x86Var
(define (location? atom)
  (match atom
    [(or (Reg _) (Deref _ _) (Var _)) #t]
    [_ #f]))
(define caller-saved-registers (map Reg '(rax rcx rdx rsi rdi r8 r9 r10 r11)))
(define (locations-written instr)
  (filter location? (match instr
    [(Instr (or 'addq 'subq 'movq) (list _ b)) (list b)]
    [(Instr (or 'negq 'pushq 'popq) (list a)) (list a)]
    [(Callq _ arity) caller-saved-registers]
    [(Retq) (list (Reg 'rax))]
    [(Jmp _) (error "(locations-read (Jmp _)): shouldn't call me")])))
(define (uncover-live p)
  (define argument-passing-registers (map Reg '(rdi rsi rdx rcx r8 r9)))
  (define (arity-to-regs n)
    (take argument-passing-registers (max n 6)))
  (define (locations-read instr)
    (filter location? (match instr
      [(Instr (or 'addq 'subq 'negq) args) args]
      [(Instr 'movq (list a b)) (list a)]
      [(Instr (or 'pushq 'popq) _) '()]
      [(Callq _ arity) (arity-to-regs arity)]
      [(Retq) (list (Reg 'rax))]
      [(Jmp _) (error "(locations-read (Jmp _)): shouldn't call me")])))
  (define (step L-after instr)
    (set-union (set-subtract L-after (locations-written instr)) (locations-read instr)))
  (define (gen-L-befores instrs init-set)
    (foldr (lambda (instr acc) (cons (step (car acc) instr) acc)) (list init-set) instrs))
  (match p
    [(X86Program info (list (cons 'start (Block start-info start-instrs))))
     (let* ([butlast (lambda (lst) (take lst (- (length lst) 1)))]
            [start-L-befores (gen-L-befores (butlast start-instrs) (map Reg '(rax rsp)))])
       (X86Program info (list
         (cons 'start (Block (list (cons 'live-afters (cdr start-L-befores))) start-instrs)))))]))

(define (build-interference p)
  (define (build-graph live-afters instrs locals)
    (define gr (undirected-graph '()))
    (for ([location (append locals (map Reg '(rax rbx rcx rdx rsi rdi rsp rbp r8 r9 r10 r11 r12 r13 r14 r15)))])
      (add-vertex! gr location))
    (for ([live-set live-afters]
          [instr instrs])
      (define ds (locations-written instr))
      (match instr
        [(Instr 'movq (list a b))
         (for ([v live-set]
               #:when (and (not (equal? v a)) (not (equal? v b))))
           (add-edge! gr v b))]
        [_
         (for ([v live-set])
           (for ([d ds]
                 #:when (not (equal? v d)))
             (add-edge! gr v d)))]))
    gr)
  (match p
    [(X86Program info (list (cons 'start (Block (list (cons 'live-afters live-afters)) instrs))))
     (X86Program info (list (cons 'start (Block (list (cons 'conflicts (build-graph live-afters instrs (map (lambda (p) (Var (car p))) (dict-ref info 'locals-types))))) instrs))))]))

(define callee-saved-registers (map Reg '(rbx rsp rbp r12 r13 r14 r15)))
(define (allocate-registers p)
  (define color->reg
    (list
      (cons 0 (Reg 'rcx))
      (cons 1 (Reg 'rdx))
      (cons 2 (Reg 'rsi))
      (cons 3 (Reg 'rdi))
      (cons 4 (Reg 'r8))
      (cons 5 (Reg 'r9))
      (cons 6 (Reg 'r10))
      (cons 7 (Reg 'rbx))
      (cons 8 (Reg 'r12))
      (cons 9 (Reg 'r13))
      (cons 10 (Reg 'r14))
      (cons -1 (Reg 'rax))
      (cons -2 (Reg 'rsp))
      (cons -3 (Reg 'rbp))
      (cons -4 (Reg 'r11))
      (cons -5 (Reg 'r15))))
  (define (color-graph interference locals)
    (define location->color (map (lambda (p) (cons (cdr p) (car p))) color->reg))
    (struct Sat (location forbids))
    (define queue (make-pqueue (lambda (a b) (>= (length (Sat-forbids a)) (length (Sat-forbids b))))))
    (define local->handle '())
    (define (get-saturation v)
      (concat (for/list ([u (in-neighbors interference v)])
        (if (dict-has-key? location->color u)
          (list (dict-ref location->color u))
          '()))))
    (define (greedy-color forbids)
      (sequence-ref (sequence-filter (lambda (n) (not (set-member? forbids n))) (in-naturals 0)) 0))
    (for ([lc locals])
      (let ([hdl (pqueue-push! queue (Sat lc (get-saturation lc)))])
        (set! local->handle (dict-set local->handle lc hdl))))
    (for ([i (in-range (pqueue-count queue))])
      (let* ([v (pqueue-pop! queue)]
             [c (greedy-color (Sat-forbids v))])
        ;(printf "v:~a,~a c:~v\n" (Sat-location v) (Sat-forbids v) c)
        (set! location->color (dict-set location->color (Sat-location v) c))
        (for ([u (in-neighbors interference (Sat-location v))]
               #:when (not (Reg? u)))
          (let ([hdl (dict-ref local->handle u)])
            (set-node-key! hdl (Sat u (get-saturation u)))
            (pqueue-decrease-key! queue hdl)))))
    location->color)
  (define (allocate location->color num-regs)
    (for/list ([l2c location->color])
      (cons (car l2c)
        (if (>= (cdr l2c) num-regs)
          (Deref 'rbp (* -8 (+ 1 (- (cdr l2c) num-regs))))
          (dict-ref color->reg (cdr l2c))))))
  (define (transform-instr instr transform-variable)
    (define (transform-arg arg)
      (match arg
        [(Var x) (transform-variable x)]
        [_ arg]))
    (match instr
      [(Instr op args) (Instr op (map transform-arg args))]
      [_ instr]))
  (define (variable-allocation allocation)
    (filter (lambda (p) (Var? (car p))) allocation))
  (define (used-callee-saved-registers allocation)
    (set-intersect callee-saved-registers (map cdr (variable-allocation allocation))))
  (define (stack-variables-size allocation)
    (define (on-stack? arg)
      (match arg
        [(Deref 'rbp _) #t]
        [_ #f]))
    (* 8 (slow-set-count (filter on-stack? (map cdr (variable-allocation allocation))))))
  (match p
    [(X86Program info (list (cons 'start (Block block-info instrs))))
     (define location->color
       (color-graph
         (dict-ref block-info 'conflicts)
         (map (lambda (p) (Var (car p))) (dict-ref info 'locals-types))))
     (define allocation (allocate location->color 11))
     (define (transform-variable x)
       (dict-ref allocation (Var x)))
     (define new-info
       (list
         (cons 'used-callee-saved-registers (used-callee-saved-registers allocation))
         (cons 'stack-variables-size (stack-variables-size allocation))))
     (X86Program (dict-merge info new-info) (list (cons 'start (Block block-info (map (lambda (instr) (transform-instr instr transform-variable)) instrs)))))]))

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (define (patch instr)
    (match instr
      [(Instr op (list a b)) #:when (equal? a b)
       (list)]
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
          (cons label (Block info (concat (map patch instrs))))])))]))

;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
  (match p
    [(X86Program info blocks)
     (define used-callee-saved-registers (dict-ref info 'used-callee-saved-registers))
     (define stack-variables-size (dict-ref info 'stack-variables-size))
     (define (align-to-16 x)
       (let ([rem (remainder x 16)])
         (if (> rem 0)
           (+ x (- 16 rem))
           x)))
     (define stack-size
       (let ([esr (* 8 (slow-set-count used-callee-saved-registers))])
         (- (align-to-16 (+ stack-variables-size esr)) esr)))
     (define save-registers
       (map (lambda (r) (Instr 'pushq (list r))) used-callee-saved-registers))
     (define restore-registers
       (map (lambda (r) (Instr 'popq (list r))) (reverse used-callee-saved-registers)))
     (X86Program info (append blocks (list
       (cons 'main (Block '() (concat (list
         (list
           (Instr 'pushq (list (Reg 'rbp)))
           (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))
           (Instr 'subq (list (Imm stack-size) (Reg 'rsp))))
         save-registers
         (list
           (Jmp 'start))))))
       (cons 'conclusion (Block '() (concat (list
         restore-registers
         (list
           (Instr 'addq (list (Imm stack-size) (Reg 'rsp)))
           (Instr 'popq (list (Reg 'rbp)))
           (Retq)))))))))]))
  
;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( ("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
     ;; Uncomment the following passes as you finish them.
     ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
     ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
     ("instruction selection" ,select-instructions ,interp-x86-0)
     ("liveness analysis" ,uncover-live ,interp-x86-0)
     ("build interference graph" ,build-interference ,interp-x86-0)
     ("allocate registers" ,allocate-registers ,interp-x86-0)
     ("patch instructions" ,patch-instructions ,interp-x86-0)
     ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))

#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Lif.rkt")
(require "interp-Cvar.rkt")
(require "interp-Cif.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Lif.rkt")
(require "type-check-Cvar.rkt")
(require "type-check-Cif.rkt")
(require "utilities.rkt")
(provide (all-defined-out))
(require "interp.rkt")
(require graph)
(require "priority_queue.rkt")
(require "multigraph.rkt")

(define (dict-merge a b)
  (for ([p b])
    (set! a (dict-set a (car p) (cdr p))))
  a)

(define (concat lsts) (apply append lsts))

(define (slow-set-count s) (set-count (if (set? s) s (list->set s))))

(define (shrink p)
  (define (shrink-exp exp)
    (match exp
      [(or (Int _) (Var _) (Bool _)) exp]
      [(If c t e) (If (shrink-exp c) (shrink-exp t) (shrink-exp e))]
      [(Let x e body) (Let x (shrink-exp e) (shrink-exp body))]
      [(Prim 'and (list a b)) (If (shrink-exp a) (shrink-exp b) (Bool #f))]
      [(Prim 'or (list a b)) (If (shrink-exp a) (Bool #t) (shrink-exp b))]
      [(Prim op args) (Prim op (map shrink-exp args))]))
  (match p
    [(Program info exp) (Program info (shrink-exp exp))]))

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x)
       (Var (dict-ref env x))]
      [(Let x e body)
       (letrec ([fresh
                 (lambda (cand)
                   (if (dict-has-key? env cand)
                     (fresh (string->symbol (string-append (symbol->string cand) "'")))
                     cand))]
                [new-x (fresh x)])
         (Let new-x ((uniquify-exp env) e) ((uniquify-exp (dict-set env x new-x)) body)))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))]
      [(If c t e) (If ((uniquify-exp env) c) ((uniquify-exp env) t) ((uniquify-exp env) e))]
      [_ e])))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (define (unzip lst) (foldr (lambda (p acc) (cons (cons (car p) (car acc)) (cons (cdr p) (cdr acc)))) (cons '() '()) lst))
  (define (rco-exp e)
    (match e
      [(If c t e) (If (rco-exp c) (rco-exp t) (rco-exp e))]
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
      [(If _ _ _) 
       (let ([ie (gensym 'tmp.if)])
         (cons (list (cons ie (rco-exp e))) (Var ie)))]
      [(Let _ _ _)
       (let ([le (gensym 'tmp.let)])
         (cons (list (cons le (rco-exp e))) (Var le)))]
      [(Prim op args)
       (letrec ([x (gensym (symbol-append 'tmp. op))]
                [bindings-and-atoms (unzip (map rco-atom args))]
                [bindings (concat (car bindings-and-atoms))])
         (cons (append bindings (list (cons x (Prim op (cdr bindings-and-atoms))))) (Var x)))]
      [_ (cons '() e)]))
  (match p
    [(Program info e) (Program info (rco-exp e))]))

;; explicate-control : R1 -> C0
(define (explicate-control p)
  (define blocks '())
  (define (emit-block symbol block)
    (if (Goto? block)
      block
      (let ([label (gensym symbol)])
        (set! blocks (dict-set blocks label block))
        (Goto label))))
  (define (explicate-if c t e)
    (match c
      [(Bool b)
       (if b t e)]
      [(Var x)
       (IfStmt (Prim 'eq? (list (Var x) (Bool #t)))
         (emit-block 'then t)
         (emit-block 'else e))]
      [(Prim 'not (list a))
       (IfStmt (Prim 'eq? (list a (Bool #f)))
         (emit-block 'then t)
         (emit-block 'else e))]
      [(Prim op args) #:when (set-member? '(eq? < <= > >=) op) ;TODO: check this
       (IfStmt c (emit-block 'then t) (emit-block 'else e))]
      [(If c2 t2 e2)
       (let ([goto-t (emit-block 'then t)]
             [goto-e (emit-block 'else e)])
         (explicate-if c2 (explicate-if t2 goto-t goto-e) (explicate-if e2 goto-t goto-e)))]
      [(Let x e body)
       (explicate-let x e (explicate-if body t e))]
      [_ (error "explicate-if: unhandled case")]))
  (define (explicate-let x e cont)
    (match e
      [(If c t e)
       (let ([goto-cont (emit-block 'let.body cont)])
         (explicate-if c (explicate-let x t goto-cont) (explicate-let x e goto-cont)))]
      [(Let x2 e2 body) (explicate-let x2 e2 (explicate-let x body cont))]
      [_ (Seq (Assign (Var x) e) cont)]))
  (define (explicate-exp e)
    (match e
      [(If c t e) (explicate-if c (explicate-exp t) (explicate-exp e))]
      [(Let x e body) (explicate-let x e (explicate-exp body))]
      [_ (Return e)]))
  (match p
    [(Program info e) (CProgram info (let ([start (explicate-exp e)]) (dict-set blocks 'start start)))]))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (define cmp->cc
    '((eq? . e) (< . l) (<= . le) (> . g) (>= . ge)))
  (define (si-atom atom)
    (match atom
      [(Int i) (Imm i)]
      [(Bool b) (if b (Imm 1) (Imm 0))]
      [(Var x) (Var x)]))
  (define (si-stmt s)
    (match s
      [(Assign x (Prim 'read '())) (list (Callq 'read_int 0) (Instr 'movq (list (Reg 'rax) x)))]
      [(Assign x (Prim '- (list a)))
       (if (equal? x a)
         (list (Instr 'negq (list a)))
         (list (Instr 'movq (list (si-atom a) x)) (Instr 'negq (list x))))]
      [(Assign x (Prim '- (list a b)))
       (if (equal? x a)
         (list (Instr 'subq (list (si-atom b) a)))
         (list (Instr 'movq (list (si-atom a) x)) (Instr 'subq (list (si-atom b) x))))]
      [(Assign x (Prim '+ (list a b)))
       (cond
        [(equal? x a) (list (Instr 'addq (list (si-atom b) a)))]
        [(equal? x b) (list (Instr 'addq (list (si-atom a) b)))]
        [else (list (Instr 'movq (list (si-atom a) x)) (Instr 'addq (list (si-atom b) x)))])]
      [(Assign x (Prim 'not (list a)))
       (if (equal? x a)
         (list (Instr 'xorq (list (Imm 1) x)))
         (list (Instr 'movq (list (si-atom a) x)) (Instr 'xorq (list (Imm 1) x))))]
      [(Assign x (Prim op (list a b))) #:when (set-member? (dict-keys cmp->cc) op)
       (list (Instr 'cmpq (list (si-atom b) (si-atom a))) (Instr 'set (list (dict-ref cmp->cc op) (ByteReg 'al))) (Instr 'movzbq (list (ByteReg 'al) x)))]
      [(Assign x atom) (list (Instr 'movq (list (si-atom atom) x)))]))
  (define (si-tail tail)
    (match tail
      [(Goto label) (list (Jmp label))]
      [(IfStmt (Prim op (list a b)) (Goto then-label) (Goto else-label))
       (list
         (Instr 'cmpq (list (si-atom b) (si-atom a)))
         (JmpIf (dict-ref cmp->cc op) then-label)
         (Jmp else-label))]
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
    [(Instr (or 'addq 'subq 'xorq 'movq 'movzbq) (list _ b)) (list b)]
    [(Instr (or 'negq 'pushq 'popq) (list a)) (list a)]
    [(Instr 'set (list _ a)) (list a)]
    [(Instr 'cmpq _) '()]
    [(Callq _ arity) caller-saved-registers]
    [(Retq) (list (Reg 'rax))]
    [(or (Jmp _) (JmpIf _ _)) '()]
    [_ (error 'locations-written "unhandled case: ~a" (Instr-name instr))])))
(define (enlarge-reg reg)
  (Reg (match (Reg-name reg)
    [(or 'ah 'al) 'rax]
    [(or 'bh 'bl) 'rbx]
    [(or 'ch 'cl) 'rcx]
    [(or 'dh 'dl) 'rdx])))
(define (uncover-live p)
  (define argument-passing-registers (map Reg '(rdi rsi rdx rcx r8 r9)))
  (define (arity-to-regs n)
    (take argument-passing-registers (max n 6)))
  (define (locations-read instr)
    (filter location? (match instr
      [(Instr (or 'addq 'subq 'xorq 'cmpq 'negq) args) args]
      [(Instr 'movq (list a _)) (list a)]
      [(Instr 'movzbq (list a _)) (enlarge-reg a)]
      [(Instr (or 'pushq 'popq) _) '()]
      [(Callq _ arity) (arity-to-regs arity)]
      [(Retq) (list (Reg 'rax))]
      [_ (error 'locations-read "unhandled case: ~a" (Instr-name instr))])))
  (define (step live-after instr)
    (match instr
      [(Jmp label) (dict-ref label->live-before label)]
      [(JmpIf _ label) (set-union live-after (dict-ref label->live-before label))]
      [_ (set-union (set-subtract live-after (locations-written instr)) (locations-read instr))]))
  (define label->live-before '((conclusion . ())))
  (define (sorted-labels blocks)
    (let ([gr (make-multigraph '())])
      (for ([label-and-block blocks])
        (match label-and-block
          [(cons curr-label (Block _ instrs))
           (add-vertex! gr curr-label)
           (for ([instr instrs])
             (match instr
               [(or (Jmp label) (JmpIf _ label))
                (add-vertex! gr label)
                (add-directed-edge! gr label curr-label)]
               [_ '()]))]))
      (filter (lambda (lbl) (dict-has-key? blocks lbl)) (tsort gr))))
  (define (gen-live-befores instrs init-set)
    (foldr (lambda (instr acc) (cons (step (car acc) instr) acc)) (list init-set) instrs))
  (define (block-live-afters label instrs)
    (let ([sets (gen-live-befores instrs '())])
      (set! label->live-before (dict-set label->live-before label (car sets)))
      (cdr sets)))
  (match p
    [(X86Program info blocks)
     (X86Program info
       (for/list ([label-and-block (map (lambda (lbl) (cons lbl (dict-ref blocks lbl))) (sorted-labels blocks))])
         (match label-and-block
           [(cons label (Block block-info instrs))
            (cons label (Block (dict-set block-info 'live-afters (block-live-afters label instrs)) instrs))])))]))

(define (build-interference p)
  (define gr (undirected-graph '()))
  (define (init-graph locals)
    (for ([location (append locals (map Reg '(rax rbx rcx rdx rsi rdi rsp rbp r8 r9 r10 r11 r12 r13 r14 r15)))])
      (add-vertex! gr location)))
  (define (update-graph live-afters instrs)
    (for ([live-set live-afters]
          [instr instrs])
      (define ds (locations-written instr))
      (match instr
        [(Instr 'movq (list a b))
         (for ([v live-set]
               #:when (and (not (equal? v a)) (not (equal? v b))))
           (add-edge! gr v b))]
        [(Instr 'movzbq (list a b))
         (for ([v live-set]
               #:when (and (not (equal? v (enlarge-reg a))) (not (equal? v b))))
           (add-edge! gr v b))]
        [_
         (for ([v live-set])
           (for ([d ds]
                 #:when (not (equal? v d)))
             (add-edge! gr v d)))])))
  (match p
    [(X86Program info blocks)
     (init-graph (map (lambda (p) (Var (car p))) (dict-ref info 'locals-types)))
     (for ([label-and-block blocks])
       (match label-and-block
         [(cons label (Block block-info instrs))
          (update-graph (dict-ref block-info 'live-afters) instrs)]))
     (X86Program (dict-set info 'conflicts gr) blocks)]))

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
    [(X86Program info blocks)
     (define location->color
       (color-graph
         (dict-ref info 'conflicts)
         (map (lambda (p) (Var (car p))) (dict-ref info 'locals-types))))
     (define allocation (allocate location->color 11))
     (define (transform-variable x)
       (dict-ref allocation (Var x)))
     (define new-info
       (list
         (cons 'used-callee-saved-registers (used-callee-saved-registers allocation))
         (cons 'stack-variables-size (stack-variables-size allocation))))
     (X86Program (dict-merge info new-info)
       (for/list ([label-and-block blocks])
         (match label-and-block
           [(cons label (Block block-info instrs))
            (cons label (Block block-info (map (lambda (instr) (transform-instr instr transform-variable)) instrs)))])))]))

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (define (patch instr)
    (match instr
      [(Instr op (list a b)) #:when (equal? a b)
       '()]
      [(Instr op (list (Deref reg1 off1) (Deref reg2 off2)))
       (list
         (Instr 'movq (list (Deref reg1 off1) (Reg 'rax)))
         (Instr op (list (Reg 'rax) (Deref reg2 off2))))]
      [(Instr 'cmpq (list a (Imm b)))
       (list
         (Instr 'movq (list (Imm b) (Reg 'rax)))
         (Instr 'cmpq (list a (Reg 'rax))))]
      [(Instr 'movzbq (list a b)) #:when (not (Reg? b))
       (list
         (Instr 'movzbq (list a (Reg 'rax)))
         (Instr 'movq (list (Reg 'rax) b)))]
      ; [(Instr (or 'addq 'subq 'xorq) (list (Imm 0) _))
      ;  '()]
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
  `( ("shrink" ,shrink ,interp-Lif ,type-check-Lif)
     ("uniquify" ,uniquify ,interp-Lif ,type-check-Lif)
     ("remove complex opera*" ,remove-complex-opera* ,interp-Lif ,type-check-Lif)
     ("explicate control" ,explicate-control ,interp-Cif ,type-check-Cif)
     ("instruction selection" ,select-instructions ,interp-x86-1)
     ("liveness analysis" ,uncover-live ,interp-x86-1)
     ("build interference graph" ,build-interference ,interp-x86-1)
     ("allocate registers" ,allocate-registers ,interp-x86-1)
     ("patch instructions" ,patch-instructions ,interp-x86-1)
     ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-1)
     ))


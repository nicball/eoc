#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lwhile.rkt")
(require "interp-Cwhile.rkt")
(require "type-check-Lwhile.rkt")
(require "type-check-Cwhile.rkt")
(require "utilities.rkt")
(provide (all-defined-out))
(require "interp.rkt")
(require graph)
(require "priority_queue.rkt")
(require "multigraph.rkt")
(require data/queue)

(define (concat lsts) (apply append lsts))

(define (set-filter p s) (list->set (filter p (set->list s))))

(define/match (shrink p)
  [((Program info exp))
   (define/match (shrink-exp exp)
     [((or (Void) (Int _) (Var _) (Bool _))) exp]
     [((WhileLoop c e)) (WhileLoop (shrink-exp c) (shrink-exp e))]
     [((SetBang x e)) (SetBang x (shrink-exp e))]
     [((Begin effs e)) (Begin (map shrink-exp effs) (shrink-exp e))]
     [((If c t e)) (If (shrink-exp c) (shrink-exp t) (shrink-exp e))]
     [((Let x e body)) (Let x (shrink-exp e) (shrink-exp body))]
     [((Prim 'and (list a b))) (If (shrink-exp a) (shrink-exp b) (Bool #f))]
     [((Prim 'or (list a b))) (If (shrink-exp a) (Bool #t) (shrink-exp b))]
     [((Prim op args)) (Prim op (map shrink-exp args))])
   (Program info (shrink-exp exp))])

(define (uniquify-exp env)
  (match-lambda
    [(SetBang x e) (SetBang x ((uniquify-exp env) e))]
    [(Begin effs e) (Begin (map (uniquify-exp env) effs) ((uniquify-exp env) e))]
    [(WhileLoop c e) (WhileLoop ((uniquify-exp env) c) ((uniquify-exp env) e))]
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
    [e e]))

;; uniquify : R1 -> R1
(define/match (uniquify p)
  [((Program info e)) (Program info ((uniquify-exp (hash)) e))])

(define/match (uncover-get! p)
  [((Program info e))
   (define/match (collect-set! exp)
     [((SetBang x e)) (set-union (set x) (collect-set! e))]
     [((Begin effs e)) (apply set-union (collect-set! e) (map collect-set! effs))]
     [((WhileLoop c e)) (set-union (uncover-get! c) (uncover-get! e))]
     [((or (Void) (Bool _) (Var _) (Int _))) (set)]
     [((If c t e)) (set-union (collect-set! c) (collect-set! t) (collect-set! e))]
     [((Let x e body)) (set-union (collect-set! e) (collect-set! body))]
     [((Prim op args)) (apply set-union (map collect-set! args))])
   (define/match (uncover-get!-exp e)
     [((or (Void) (Bool _) (Var _) (Int _))) e]
     [((SetBang x e)) (SetBang x (uncover-get!-exp e))]
     [((Begin effs e)) (Begin (map uncover-get!-exp effs) (uncover-get!-exp e))]
     [((WhileLoop c e)) (WhileLoop (uncover-get!-exp c) (uncover-get!-exp e))]
     [((If c t e)) (If (uncover-get!-exp c) (uncover-get!-exp t) (uncover-get!-exp e))]
     [((Let x e body)) (Let x (uncover-get!-exp e) (uncover-get!-exp body))]
     [((Prim op args))
      (let ([muts (apply set-union (map collect-set! args))])
        (Prim op
          (for/list ([arg args])
            (match (uncover-get!-exp arg)
              [(Var x) #:when (set-member? muts x)
               (GetBang x)]
              [e e]))))])
   (Program info (uncover-get!-exp e))])

;; remove-complex-opera* : R1 -> R1
(define/match (remove-complex-opera* p)
  [((Program info e))
   (define (unzip lst) (foldr (lambda (p acc) (cons (cons (car p) (car acc)) (cons (cdr p) (cdr acc)))) (cons '() '()) lst))
   (define/match (rco-exp e)
     [((GetBang x)) (error 'rco-exp "impossible")]
     [((SetBang x e)) (SetBang x (rco-exp e))]
     [((Begin effs e)) (Begin (map rco-exp effs) (rco-exp e))]
     [((WhileLoop c e)) (WhileLoop (rco-exp c) (rco-exp e))]
     [((If c t e)) (If (rco-exp c) (rco-exp t) (rco-exp e))]
     [((Let x e body)) (Let x (rco-exp e) (rco-exp body))]
     [((Prim op args))
      (letrec ([bindings-and-atoms (unzip (map rco-atom args))]
               [bindings (concat (car bindings-and-atoms))]
               [list-to-lets
                (lambda (lst body)
                  (if (pair? lst)
                    (Let (caar lst) (cdar lst) (list-to-lets (cdr lst) body))
                    body))])
        (list-to-lets bindings (Prim op (cdr bindings-and-atoms))))]
     [(_) e])
   (define/match (rco-atom e)
     [((GetBang x))
      (let ([xx (gensym x)])
        (cons (list (cons xx (Var x))) (Var xx)))]
     [((Begin _ _))
      (let ([be (gensym 'begin)])
        (cons (list (cons be (rco-exp e))) (Var be)))]
     [((If _ _ _)) 
      (let ([ie (gensym 'tmp.if)])
        (cons (list (cons ie (rco-exp e))) (Var ie)))]
     [((Let _ _ _))
      (let ([le (gensym 'tmp.let)])
        (cons (list (cons le (rco-exp e))) (Var le)))]
     [((Prim op _))
      (let ([pe (gensym (symbol-append 'tmp. op))])
        (cons (list (cons pe (rco-exp e))) (Var pe)))]
     [(_) (cons '() e)])
   (Program info (rco-exp e))])

;; explicate-control : R1 -> C0
(define/match (explicate-control p)
  [((Program info e))
   (define blocks (make-hash))
   (define (emit-named-block label block)
     (if (Goto? block)
       block
       (begin
         (dict-set! blocks label block)
         (Goto label))))
   (define (emit-block symbol block)
     (emit-named-block (gensym symbol) block))
   (define (explicate-effects effs cont)
     (match effs
       ['() cont]
       [(cons (WhileLoop c e) effs) 
        (let ([loop-head-label (gensym 'loop.head)]
              [loop-body-label (gensym 'loop.body)])
          (emit-named-block loop-body-label (explicate-effects (list e) (Goto loop-head-label)))
          (emit-named-block loop-head-label (explicate-if c (Goto loop-body-label) (explicate-effects effs cont))))]
       [(cons (SetBang x e) effs)
        (explicate-assign x e (explicate-effects effs cont))]
       [(cons (Begin effs2 e2) effs)
        (explicate-effects (append effs2 (list e2) effs) cont)]
       [(cons (Prim 'read '()) effs)
        (Seq (Prim 'read '()) (explicate-effects effs cont))]
       [(cons (or (Prim _ _) (Int _) (Var _) (Bool _) (Void)) effs)
        (explicate-effects effs cont)]
       [(cons (If c t e) effs)
        (let ([cont (emit-block 'effs (explicate-effects effs cont))])
          (explicate-if c (explicate-effects (list t) cont) (explicate-effects (list e) cont)))]
       [(cons (Let x e body) effs)
        (explicate-assign x e (explicate-effects (cons body effs) cont))]))
   (define (explicate-if c t e)
     (match c
       [(Begin effs c) (explicate-effects effs (explicate-if c t e))]
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
        (explicate-assign x e (explicate-if body t e))]
       [_ (error "explicate-if: unhandled case")]))
   (define (explicate-assign x e cont)
     (match e
       [(SetBang _ _) (error 'explicate-assign "set! cannot be assigned to ~a" x)]
       [(GetBang _) (error 'explicate-assign "impossible")]
       [(Begin effs e) (explicate-effects effs (explicate-assign x e cont))]
       [(WhileLoop _ _) (error 'explicate-assign "while cannot be assigned to ~a" x)]
       [(If c t e)
        (let ([goto-cont (emit-block 'let.body cont)])
          (explicate-if c (explicate-assign x t goto-cont) (explicate-assign x e goto-cont)))]
       [(Let x2 e2 body) (explicate-assign x2 e2 (explicate-assign x body cont))]
       [_ (Seq (Assign (Var x) e) cont)]))
   (define/match (explicate-tail e)
     [((SetBang _ _)) (error 'explicate-tail "set! cannot be in tail position")]
     [((GetBang _)) (error 'explicate-tail "impossible")]
     [((Begin effs e)) (explicate-effects effs (explicate-tail e))]
     [((WhileLoop _ _)) (error 'explicate-tail "while cannot be in tail position")]
     [((If c t e)) (explicate-if c (explicate-tail t) (explicate-tail e))]
     [((Let x e body)) (explicate-assign x e (explicate-tail body))]
     [(_) (Return e)])
   (CProgram info (let ([start (explicate-tail e)])
     (dict-set! blocks 'start start)
     (make-immutable-hash (hash->list blocks))))])

;; select-instructions : C0 -> pseudo-x86
(define/match (select-instructions p)
  [((CProgram info blocks))
   (define cmp->cc
     '((eq? . e) (< . l) (<= . le) (> . g) (>= . ge)))
   (define/match (si-atom atom)
     [((Int i)) (Imm i)]
     [((Bool b)) (if b (Imm 1) (Imm 0))]
     [((Var x)) (Var x)]
     [((Void)) (Imm 0)])
   (define/match (si-stmt s)
     [((Assign x (Prim 'read '()))) (list (Callq 'read_int 0) (Instr 'movq (list (Reg 'rax) x)))]
     [((Assign x (Prim '- (list a))))
      (if (equal? x a)
        (list (Instr 'negq (list a)))
        (list (Instr 'movq (list (si-atom a) x)) (Instr 'negq (list x))))]
     [((Assign x (Prim '- (list a b))))
      (if (equal? x a)
        (list (Instr 'subq (list (si-atom b) a)))
        (list (Instr 'movq (list (si-atom a) x)) (Instr 'subq (list (si-atom b) x))))]
     [((Assign x (Prim '+ (list a b))))
      (cond
       [(equal? x a) (list (Instr 'addq (list (si-atom b) a)))]
       [(equal? x b) (list (Instr 'addq (list (si-atom a) b)))]
       [else (list (Instr 'movq (list (si-atom a) x)) (Instr 'addq (list (si-atom b) x)))])]
     [((Assign x (Prim 'not (list a))))
      (if (equal? x a)
        (list (Instr 'xorq (list (Imm 1) x)))
        (list (Instr 'movq (list (si-atom a) x)) (Instr 'xorq (list (Imm 1) x))))]
     [((Assign x (Prim op (list a b)))) #:when (set-member? (dict-keys cmp->cc) op)
      (list (Instr 'cmpq (list (si-atom b) (si-atom a))) (Instr 'set (list (dict-ref cmp->cc op) (ByteReg 'al))) (Instr 'movzbq (list (ByteReg 'al) x)))]
     [((Assign x atom)) (list (Instr 'movq (list (si-atom atom) x)))]
     [((Prim 'read '())) (list (Callq 'read_int 0))])
   (define/match (si-tail tail)
     [((Goto label)) (list (Jmp label))]
     [((IfStmt (Prim op (list a b)) (Goto then-label) (Goto else-label)))
      (list
        (Instr 'cmpq (list (si-atom b) (si-atom a)))
        (JmpIf (dict-ref cmp->cc op) then-label)
        (Jmp else-label))]
     [((Return e)) (append (si-stmt (Assign (Reg 'rax) e)) (list (Jmp 'conclusion)))]
     [((Seq stmt tail)) (append (si-stmt stmt) (si-tail tail))])
   (X86Program info (hash-map/copy blocks (lambda (label block) (values label (Block '() (si-tail block))))))])

;; uncover-live : x86Var -> x86Var
(define/match (location? atom)
  [((or (Reg _) (Deref _ _) (Var _))) #t]
  [(_) #f])
(define caller-saved-registers (map Reg '(rax rcx rdx rsi rdi r8 r9 r10 r11)))
(define (locations-written instr)
  (set-filter location? (match instr
    [(Instr (or 'addq 'subq 'xorq 'movq 'movzbq) (list _ b)) (set b)]
    [(Instr (or 'negq 'pushq 'popq) (list a)) (set a)]
    [(Instr 'set (list _ a)) (set a)]
    [(Instr 'cmpq _) (set)]
    [(Callq _ arity) (list->set caller-saved-registers)]
    [(Retq) (set (Reg 'rax))]
    [(or (Jmp _) (JmpIf _ _)) (set)]
    [_ (error 'locations-written "unhandled case: ~a" (Instr-name instr))])))
(define (enlarge-reg reg)
  (Reg (match (Reg-name reg)
    [(or 'ah 'al) 'rax]
    [(or 'bh 'bl) 'rbx]
    [(or 'ch 'cl) 'rcx]
    [(or 'dh 'dl) 'rdx])))
(define/match (uncover-live p)
  [((X86Program info blocks))
   (define argument-passing-registers (map Reg '(rdi rsi rdx rcx r8 r9)))
   (define (arity-to-regs n)
     (list->set (take argument-passing-registers (max n 6))))
   (define (locations-read instr)
     (set-filter location? (match instr
       [(Instr (or 'addq 'subq 'xorq 'cmpq 'negq) args) (list->set args)]
       [(Instr 'movq (list a _)) (set a)]
       [(Instr 'movzbq (list a _)) (set (enlarge-reg a))]
       [(Instr (or 'pushq 'popq) _) (set)]
       [(Callq _ arity) (arity-to-regs arity)]
       [(Retq) (set (Reg 'rax))]
       [_ (error 'locations-read "unhandled case: ~a" (Instr-name instr))])))
   (define (step live-after instr)
     (match instr
       [(or (Jmp _) (JmpIf _ _)) live-after]
       [_ (set-union (set-subtract live-after (locations-written instr)) (locations-read instr))]))
   (define label->live-afters (make-hash))
   (define (gen-live-befores instrs live-after)
     (foldr (lambda (instr acc) (cons (step (car acc) instr) acc)) (list live-after) instrs))
   (define (transfer label live-after)
     (let* ([instrs (Block-instr* (dict-ref blocks label))]
            [sets (gen-live-befores instrs live-after)])
       (dict-set! label->live-afters label (cdr sets))
       (car sets)))
   (define cfg
     (let ([gr (make-multigraph '())])
      (for ([(curr-label block) (in-dict blocks)])
        (add-vertex! gr curr-label)
        (for ([instr (Block-instr* block)])
          (match instr
            [(or (Jmp label) (JmpIf _ label)) #:when (dict-has-key? blocks label)
             (add-vertex! gr label)
             (add-directed-edge! gr label curr-label)]
            [_ '()])))
       gr))
   (define (analyse-dataflow cfg transfer bottom join)
     (define label->live-before (make-hash))
     (define work-list (make-queue))
     (for ([v (in-vertices cfg)])
       (dict-set! label->live-before v bottom)
       (enqueue! work-list v))
     (define cfg-t (transpose cfg))
     (while (not (queue-empty? work-list))
       (define curr-node (dequeue! work-list))
       (define input
         (for/fold ([state bottom]) ([pred (in-neighbors cfg-t curr-node)])
           (join state (dict-ref label->live-before pred))))
       (define output (transfer curr-node input))
       (cond [(not (equal? output (dict-ref label->live-before curr-node)))
         (dict-set! label->live-before curr-node output)
         (for ([succ (in-vertices cfg)])
           (enqueue! work-list succ))]))
     label->live-before)
   (analyse-dataflow cfg transfer (set) set-union) 
   (X86Program info
     (hash-map/copy blocks (lambda (label block)
       (values label (Block (dict-set (Block-info block) 'live-afters (dict-ref label->live-afters label)) (Block-instr* block))))))])

(define/match (build-interference p)
  [((X86Program info blocks))
   (define gr (undirected-graph '()))
   (for ([location (append (map (lambda (p) (Var (car p))) (dict-ref info 'locals-types))
                           (map Reg '(rax rbx rcx rdx rsi rdi rsp rbp r8 r9 r10 r11 r12 r13 r14 r15)))])
     (add-vertex! gr location))
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
   (for ([(label block) (in-dict blocks)])
     (update-graph (dict-ref (Block-info block) 'live-afters) (Block-instr* block)))
   (X86Program (dict-set info 'conflicts gr) blocks)])

(define callee-saved-registers (map Reg '(rbx rsp rbp r12 r13 r14 r15)))
(define/match (allocate-registers p)
  [((X86Program info blocks))
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
   (define locals (map (lambda (p) (Var (car p))) (dict-ref info 'locals-types)))
   (define interference (dict-ref info 'conflicts))
   (define location->color (make-hash (map (lambda (p) (cons (cdr p) (car p))) color->reg)))
   (struct Sat (location forbids))
   (define queue (make-pqueue (lambda (a b) (>= (set-count (Sat-forbids a)) (set-count (Sat-forbids b))))))
   (define local->handle (make-hash))
   (define (get-saturation v)
     (list->set (concat (for/list ([u (in-neighbors interference v)])
       (if (dict-has-key? location->color u)
         (list (dict-ref location->color u))
         '())))))
   (define (greedy-color forbids)
     (sequence-ref (sequence-filter (lambda (n) (not (set-member? forbids n))) (in-naturals 0)) 0))
   (for ([lc locals])
     (let ([hdl (pqueue-push! queue (Sat lc (get-saturation lc)))])
       (dict-set! local->handle lc hdl)))
   (for ([i (in-range (pqueue-count queue))])
     (let* ([v (pqueue-pop! queue)]
            [c (greedy-color (Sat-forbids v))])
       ;(printf "v:~a,~a c:~v\n" (Sat-location v) (Sat-forbids v) c)
       (dict-set! location->color (Sat-location v) c)
       (for ([u (in-neighbors interference (Sat-location v))]
              #:when (not (Reg? u)))
         (let ([hdl (dict-ref local->handle u)])
           (set-node-key! hdl (Sat u (get-saturation u)))
           (pqueue-decrease-key! queue hdl)))))
   (define num-regs 11)
   (define allocation
     (make-immutable-hash
       (for/list ([(location color) (in-dict location->color)])
         (cons location
           (if (>= color num-regs)
             (Deref 'rbp (* -8 (+ 1 (- color num-regs))))
             (dict-ref color->reg color))))))
   (define (transform-instr instr)
     (define/match (transform-arg arg)
       [((Var x)) (dict-ref allocation arg)]
       [(_) arg])
     (match instr
       [(Instr op args) (Instr op (map transform-arg args))]
       [_ instr]))
   (define variable-allocation
     (list->set (filter Var? (hash-keys allocation))))
   (define used-callee-saved-registers
     (set-intersect (list->set callee-saved-registers) variable-allocation))
   (define/match (on-stack? arg)
     [((Deref 'rbp _)) #t]
     [(_) #f])
   (define stack-variables-size
     (* 8 (set-count (set-filter on-stack? variable-allocation))))
   (define new-info (list
     'used-callee-saved-registers used-callee-saved-registers
     'stack-variables-size stack-variables-size))
   (X86Program (apply dict-set* info new-info)
     (hash-map/copy blocks (lambda (label block)
       (values label (Block (Block-info block) (map transform-instr (Block-instr* block)))))))])

;; patch-instructions : psuedo-x86 -> x86
(define/match (patch-instructions p)
  [((X86Program info blocks))
   (define/match (patch instr)
     [((Instr op (list a b))) #:when (equal? a b)
      '()]
     [((Instr op (list (Deref reg1 off1) (Deref reg2 off2))))
      (list
        (Instr 'movq (list (Deref reg1 off1) (Reg 'rax)))
        (Instr op (list (Reg 'rax) (Deref reg2 off2))))]
     [((Instr 'cmpq (list a (Imm b))))
      (list
        (Instr 'movq (list (Imm b) (Reg 'rax)))
        (Instr 'cmpq (list a (Reg 'rax))))]
     [((Instr 'movzbq (list a b))) #:when (not (Reg? b))
      (list
        (Instr 'movzbq (list a (Reg 'rax)))
        (Instr 'movq (list (Reg 'rax) b)))]
     [(_) (list instr)])
   (X86Program info (hash-map/copy blocks (lambda (label block)
     (values label (Block (Block-info block) (concat (map patch (Block-instr* block))))))))])

;; prelude-and-conclusion : x86 -> x86
(define/match (prelude-and-conclusion p)
  [((X86Program info blocks))
   (define used-callee-saved-registers (dict-ref info 'used-callee-saved-registers))
   (define stack-variables-size (dict-ref info 'stack-variables-size))
   (define (align-to-16 x)
     (let ([rem (remainder x 16)])
       (if (> rem 0)
         (+ x (- 16 rem))
         x)))
   (define stack-size
     (let ([esr (* 8 (set-count used-callee-saved-registers))])
       (- (align-to-16 (+ stack-variables-size esr)) esr)))
   (define esr-order (set->list used-callee-saved-registers))
   (define save-registers
     (map (lambda (r) (Instr 'pushq (list r))) esr-order))
   (define restore-registers
     (map (lambda (r) (Instr 'popq (list r))) (reverse esr-order)))
   (X86Program info (dict-set* blocks
     'main (Block '() (concat (list
       (list
         (Instr 'pushq (list (Reg 'rbp)))
         (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))
         (Instr 'subq (list (Imm stack-size) (Reg 'rsp))))
       save-registers
       (list
         (Jmp 'start)))))
     'conclusion (Block '() (concat (list
       restore-registers
       (list
         (Instr 'addq (list (Imm stack-size) (Reg 'rsp)))
         (Instr 'popq (list (Reg 'rbp)))
         (Retq)))))))])
  
;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( ("shrink" ,shrink ,interp-Lwhile ,type-check-Lwhile)
     ("uniquify" ,uniquify ,interp-Lwhile ,type-check-Lwhile)
     ("uncover get!" ,uncover-get! ,interp-Lwhile ,type-check-Lwhile)
     ("remove complex opera*" ,remove-complex-opera* ,interp-Lwhile ,type-check-Lwhile)
     ("explicate control" ,explicate-control ,interp-Cwhile ,type-check-Cwhile)
     ("instruction selection" ,select-instructions ,interp-x86-1)
     ("liveness analysis" ,uncover-live ,interp-x86-1)
     ("build interference graph" ,build-interference ,interp-x86-1)
     ("allocate registers" ,allocate-registers ,interp-x86-1)
     ("patch instructions" ,patch-instructions ,interp-x86-1)
     ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-1)
     ))



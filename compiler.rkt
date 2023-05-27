#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lfun.rkt")
(require "interp-Lfun-prime.rkt")
(require "interp-Cfun.rkt")
(require "type-check-Lfun.rkt")
(require "type-check-Cfun.rkt")
(require "utilities.rkt")
(provide (all-defined-out))
(require "interp.rkt")
(require graph)
(require "priority_queue.rkt")
(require "multigraph.rkt")
(require data/queue)

(define (concat lsts) (apply append lsts))

(define (set-filter p s) (list->set (filter p (set->list s))))

(define (append-point sym) (symbol-append sym (string->symbol ".")))

(define (Vector? type)
  (match type
    [(list 'Vector _ ...) #t]
    [_ #f]))

(define (log fmt e) (printf fmt e) e)

(define ((induct-L f) e)
  (match e
    [(or (Int _) (Var _) (Bool _) (Void) (GetBang _) (Collect _) (Allocate _ _) (GlobalValue _) (FunRef _ _)) (f e)]
    [(Prim op args) (f (Prim op (map (induct-L f) args)))]
    [(Let x e body) (f (Let x ((induct-L f) e) ((induct-L f) body)))]
    [(If c t e) (f (If ((induct-L f) c) ((induct-L f) t) ((induct-L f) e)))]
    [(SetBang x e) (f (SetBang x ((induct-L f) e)))]
    [(Begin effs e) (f (Begin (map (induct-L f) effs) ((induct-L f) e)))]
    [(WhileLoop c e) (f (WhileLoop ((induct-L f) c) ((induct-L f) e)))]
    [(HasType e t) (f (HasType ((induct-L f) e) t))]
    [(Apply e es) (f (Apply ((induct-L f) e) (map (induct-L f) es)))]))

(define/match (shrink p)
  [((ProgramDefsExp info defs exp))
   (define shrink-exp
     (induct-L (match-lambda
       [(Prim 'and (list a b)) (If a b (Bool #f))]
       [(Prim 'or (list a b)) (If a (Bool #t) b)]
       [exp exp])))
   (define/match (shrink-Def def)
     [((Def name params rty info body))
      (Def name params rty info (shrink-exp body))])
   (ProgramDefs info (append (map shrink-Def defs) (list (shrink-Def (Def 'main '() 'Integer (hash) exp)))))])

(define (uniquify-exp env)
  (match-lambda
    [(SetBang x e) (SetBang x ((uniquify-exp env) e))]
    [(Begin effs e) (Begin (map (uniquify-exp env) effs) ((uniquify-exp env) e))]
    [(WhileLoop c e) (WhileLoop ((uniquify-exp env) c) ((uniquify-exp env) e))]
    [(Var x)
     (Var (dict-ref env x))]
    [(Let x e body)
     (letrec ([new-x (if (dict-has-key? env x) (gensym (append-point x)) x)])
       (Let new-x ((uniquify-exp env) e) ((uniquify-exp (dict-set env x new-x)) body)))]
    [(Prim op es)
     (Prim op (for/list ([e es]) ((uniquify-exp env) e)))]
    [(If c t e) (If ((uniquify-exp env) c) ((uniquify-exp env) t) ((uniquify-exp env) e))]
    [e e]))

;; uniquify : R1 -> R1
(define/match (uniquify p)
  [((ProgramDefs info defs))
   (define env
     (for/hash ([def defs])
       (values (Def-name def) (Def-name def))))
   (ProgramDefs info
     (for/list ([def defs])
       (match def
         [(Def name params rty info body)
          (define new-env
            (for/fold ([new-env env]) ([p params])
              (if (dict-has-key? env (car p))
                (dict-set new-env (car p) (gensym (append-point (car p))))
                (dict-set new-env (car p) (car p)))))
          (Def name params rty info ((uniquify-exp new-env) body))])))])

(define/match (reveal-functions p)
  [((ProgramDefs info defs))
   (define fun->arity
     (for/hash ([def defs])
       (values (Def-name def) (length (Def-param* def)))))
   (define reveal-functions-exp
     (induct-L (match-lambda
       [(Var x) #:when (dict-has-key? fun->arity x)
        (FunRef x (dict-ref fun->arity x))]
       [exp exp])))
   (ProgramDefs info
     (for/list ([def defs])
       (match def
         [(Def name params rty info body)
          (Def name params rty info (reveal-functions-exp body))])))])

(define/match (limit-functions p)
  [((ProgramDefs info defs))
   (define/match (limit-functions-Def def)
     [((Def name params rty info body)) #:when (> (length params) 6)
      (define rest-names (map car (drop params 5)))
      (define rest-types (map caddr (drop params 5)))
      (define rest-var (gensym 'rest-params.))
      (define new-params (append (take params 5) (list (list rest-var ': (cons 'Vector rest-types)))))
      (define rename-exp
        (induct-L (match-lambda
          [(Var x) #:when (set-member? rest-names x)
           (Prim 'vector-ref (list (Var rest-var) (Int (index-of rest-names x))))]
          [(Apply e es) #:when (> (length es) 6)
           (Apply e (append (take es 5) (list (Prim 'vector (drop es 5)))))]
          [exp exp])))
      (Def name new-params rty info (rename-exp body))]
     [((Def name params rty info body))
      (define rename-exp
        (induct-L (match-lambda
          [(Apply e es) #:when (> (length es) 6)
           (Apply e (append (take es 5) (list (Prim 'vector (drop es 5)))))]
          [exp exp])))
      (Def name params rty info (rename-exp body))])
   (ProgramDefs info (map limit-functions-Def defs))])

(define/match (expose-allocation p)
  [((ProgramDefs info defs))
   (define expose-allocation-exp
     (induct-L (match-lambda
       [(HasType (Prim 'vector es) type)
        (define (eval-elems es xs body)
          (match es
            [(cons e es) (Let (car xs) e (eval-elems es (cdr xs) body))]
            ['() body]))
        (define n (length es))
        (define allocation-size (* 8 (+ 1 n)))
        (define check-enough-space
          (If (Prim '< (list (Prim '+ (list (GlobalValue 'free_ptr) (Int allocation-size)))
                             (GlobalValue 'fromspace_end)))
            (Void)
            (Collect allocation-size)))
        (define vector-var (gensym 'vector.))
        (define elems-vars
          (for/list ([i (in-range n)])
            (gensym (symbol-append 'vector.elem. (append-point (string->symbol (number->string i)))))))
        (eval-elems es elems-vars
          (Begin (list check-enough-space)
            (Let vector-var (Allocate n type)
              (Begin (for/list ([i (in-range n)] [v elems-vars]) (Prim 'vector-set! (list (Var vector-var) (Int i) (Var v))))
                (Var vector-var)))))]
       [exp exp])))
   (ProgramDefs info
     (for/list ([def defs])
       (match def
         [(Def name params rty info body)
          (Def name params rty info (expose-allocation-exp body))])))])

(define/match (uncover-get! p)
  [((ProgramDefs info defs))
   (define/match (collect-set! exp)
     [((or (Collect _) (Allocate _ _) (GlobalValue _) (FunRef _ _))) (set)]
     [((Apply e es)) (apply set-union (collect-set! e) (map collect-set! es))]
     [((SetBang x e)) (set-union (set x) (collect-set! e))]
     [((Begin effs e)) (apply set-union (collect-set! e) (map collect-set! effs))]
     [((WhileLoop c e)) (set-union (uncover-get! c) (uncover-get! e))]
     [((or (Void) (Bool _) (Var _) (Int _) (GetBang _))) (set)]
     [((If c t e)) (set-union (collect-set! c) (collect-set! t) (collect-set! e))]
     [((Let x e body)) (set-union (collect-set! e) (collect-set! body))]
     [((Prim op args)) (apply set-union (set) (map collect-set! args))])
   (define uncover-get!-exp
     (induct-L (match-lambda
       [(Prim op args)
        (let ([muts (apply set-union (set) (map collect-set! args))])
          (Prim op
            (for/list ([arg args])
              (match arg
                [(Var x) #:when (set-member? muts x)
                 (GetBang x)]
                [_ arg]))))]
       [exp exp])))
   (ProgramDefs info
     (for/list ([def defs])
       (match def
         [(Def name params rty info body)
          (Def name params rty info (uncover-get!-exp body))])))])

;; remove-complex-operands : R1 -> R1
(define/match (remove-complex-operands p)
  [((ProgramDefs info defs))
   (define (unzip lst) (foldr (lambda (p acc) (cons (cons (car p) (car acc)) (cons (cdr p) (cdr acc)))) (cons '() '()) lst))
   (define rco-exp
     (induct-L (match-lambda
       [(Prim op args)
        (define-values (bindings atoms)
          (for/fold ([bindings '()] [atoms '()]) ([exp args])
            (let-values ([(bs a) (rco-atom exp)])
              (values (append bindings bs) (append atoms (list a))))))
        (for/foldr ([exp (Prim op atoms)]) ([binding bindings])
          (Let (car binding) (cdr binding) exp))]
       [(Apply f args)
        (define-values (bindings atoms)
          (for/fold ([bindings '()] [atoms '()]) ([exp (cons f args)])
            (let-values ([(bs a) (rco-atom exp)])
              (values (append bindings bs) (append atoms (list a))))))
        (for/foldr ([exp (Apply (car atoms) (cdr atoms))]) ([binding bindings])
          (Let (car binding) (cdr binding) exp))]
       [e e])))
   (define/match (exp->symbol e)
     [((Begin _ _)) (gensym 'op.begin.)]
     [((If _ _ _)) (gensym 'op.if.)]
     [((Let _ _ _)) (gensym 'op.let.)]
     [((Prim op _)) (gensym (symbol-append 'op. (append-point op)))]
     [((Collect _)) (gensym 'collect.)]
     [((Allocate _ _)) (gensym 'allocate.)]
     [((GlobalValue x)) (gensym (append-point x))]
     [((FunRef _ _)) (gensym 'fun-ref.)])
   (define/match (rco-atom e)
     [((GetBang x))
      (let ([xx (gensym (append-point x))])
        (values (list (cons xx (Var x))) (Var xx)))]
     [((or (Begin _ _) (If _ _ _) (Let _ _ _) (Prim _ _) (Collect _) (Allocate _ _) (GlobalValue _) (FunRef _ _)))
      (let ([x (exp->symbol e)])
        (values (list (cons x (rco-exp e))) (Var x)))]
     [(_) (values '() e)])
   (ProgramDefs info
     (for/list ([def defs])
       (match def
         [(Def name params rty info body)
          (Def name params rty info (rco-exp body))])))])

;; explicate-control : R1 -> C0
(define/match (explicate-control-Def def)
  [((Def name params rty info body))
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
       [(cons (Apply f args) effs)
        (define x (gensym 'not.used.))
        (explicate-assign x (Apply f args) (explicate-effects effs cont))]
       [(cons (WhileLoop c e) effs) 
        (let ([loop-head-label (gensym 'loop.head.)]
              [loop-body-label (gensym 'loop.body.)])
          (emit-named-block loop-body-label (explicate-effects (list e) (Goto loop-head-label)))
          (emit-named-block loop-head-label (explicate-if c (Goto loop-body-label) (explicate-effects effs cont))))]
       [(cons (SetBang x e) effs)
        (explicate-assign x e (explicate-effects effs cont))]
       [(cons (Begin effs2 e2) effs)
        (explicate-effects (append effs2 (list e2) effs) cont)]
       [(cons (Prim 'read '()) effs)
        (Seq (Prim 'read '()) (explicate-effects effs cont))]
       [(cons (Prim 'vector-set! args) effs)
        (Seq (Prim 'vector-set! args) (explicate-effects effs cont))]
       [(cons (Collect n) effs)
        (Seq (Collect n) (explicate-effects effs cont))]
       [(cons (or (Prim _ _) (Int _) (Var _) (Bool _) (Void) (GlobalValue _) (Allocate _ _) (FunRef _ _)) effs)
        (explicate-effects effs cont)]
       [(cons (If c t e) effs)
        (let ([cont (emit-block 'effs. (explicate-effects effs cont))])
          (explicate-if c (explicate-effects (list t) cont) (explicate-effects (list e) cont)))]
       [(cons (Let x e body) effs)
        (explicate-assign x e (explicate-effects (cons body effs) cont))]))
   (define (explicate-if c t e)
     (match c
       [(Apply f args)
        (define cond-var (gensym 'if.cond.))
        (explicate-assign cond-var (Call f args) (explicate-if (Var cond-var) t e))]
       [(Begin effs c) (explicate-effects effs (explicate-if c t e))]
       [(Bool b)
        (if b t e)]
       [(or (Var _) (GlobalValue _))
        (IfStmt (Prim 'eq? (list c (Bool #t)))
          (emit-block 'then. t)
          (emit-block 'else. e))]
       [(Prim 'not (list a))
        (IfStmt (Prim 'eq? (list a (Bool #f)))
          (emit-block 'then. t)
          (emit-block 'else. e))]
       [(Prim op args) #:when (set-member? '(eq? < <= > >=) op)
        (IfStmt c (emit-block 'then. t) (emit-block 'else. e))]
       [(If c2 t2 e2)
        (let ([goto-t (emit-block 'then. t)]
              [goto-e (emit-block 'else. e)])
          (explicate-if c2 (explicate-if t2 goto-t goto-e) (explicate-if e2 goto-t goto-e)))]
       [(Let x ee body)
        (explicate-assign x ee (explicate-if body t e))]
       [_ (error 'explicate-if "~a is not a predicate" c)]))
   (define (explicate-assign x e cont)
     (match e
       [(Apply f args) (Seq (Assign (Var x) (Call f args)) cont)]
       [(or (Collect _) (SetBang _ _) (WhileLoop _ _)) (error 'explicate-assign "~a cannot be assigned to ~a" e x)]
       [(GetBang _) (error 'explicate-assign "impossible")]
       [(Begin effs e) (explicate-effects effs (explicate-assign x e cont))]
       [(If c t e)
        (let ([goto-cont (emit-block 'let.body. cont)])
          (explicate-if c (explicate-assign x t goto-cont) (explicate-assign x e goto-cont)))]
       [(Let x2 e2 body) (explicate-assign x2 e2 (explicate-assign x body cont))]
       [_ (Seq (Assign (Var x) e) cont)]))
   (define/match (explicate-tail e)
     [((Apply f args)) (TailCall f args)]
     [((or (Collect _) (SetBang _ _) (WhileLoop _ _))) (error 'explicate-tail "~a cannot be in tail position" e)]
     [((GetBang _)) (error 'explicate-tail "impossible")]
     [((Begin effs e)) (explicate-effects effs (explicate-tail e))]
     [((If c t e)) (explicate-if c (explicate-tail t) (explicate-tail e))]
     [((Let x e body)) (explicate-assign x e (explicate-tail body))]
     [(_) (Return e)])
   (Def name params rty info (let ([start (explicate-tail body)])
     (dict-set! blocks (symbol-append name 'start) start)
     (make-immutable-hash (hash->list blocks))))])

(define/match (explicate-control p)
  [((ProgramDefs info defs))
   (ProgramDefs info (map explicate-control-Def defs))])

;; select-instructions : C0 -> pseudo-x86
(define argument-passing-registers (map Reg '(rdi rsi rdx rcx r8 r9)))

(define/match (select-instructions-Def p)
  [((Def name params _ info blocks))
   (define (vector-offset n) (* 8 (+ 1 n)))
   (define (vector-tag elem-types)
     (define pointer-mask
       (for/fold ([mask 0]) ([i (in-naturals)] [t elem-types])
         (bitwise-ior mask
           (match t
             [(list 'Vector _ ...) (arithmetic-shift 1 (+ 7 i))]
             [_ 0]))))
     (define vector-length (arithmetic-shift (length elem-types) 1))
     (bitwise-ior pointer-mask vector-length))
   (define cmp->cc
     '((eq? . e) (< . l) (<= . le) (> . g) (>= . ge)))
   (define/match (si-atom atom)
     [((Int i)) (Imm i)]
     [((Bool b)) (if b (Imm 1) (Imm 0))]
     [((Var x)) (Var x)]
     [((Void)) (Imm 0)]
     [((GlobalValue x)) (Global x)])
   (define/match (si-stmt s)
     [((Assign x (FunRef name _)))
      (list
        (Instr 'leaq (list (Global name) x)))]
     [((Assign x (Call f args)))
      (append
        (for/list ([a args] [r argument-passing-registers])
          (Instr 'movq (list (si-atom a) r)))
        (list
          (IndirectCallq (si-atom f) (length args))
          (Instr 'movq (list (Reg 'rax) x))))]
     [((Assign x (Prim 'vector-ref (list v (Int n)))))
      (list
        (Instr 'movq (list (si-atom v) (Reg 'r11)))
        (Instr 'movq (list (Deref 'r11 (vector-offset n)) x)))]
     [((Assign x (Prim 'vector-set! (list v (Int n) e))))
      (list
        (Instr 'movq (list (si-atom v) (Reg 'r11)))
        (Instr 'movq (list (si-atom e) (Deref 'r11 (vector-offset n))))
        (Instr 'movq (list (Imm 0) x)))]
     [((Assign x (Prim 'vector-length (list v))))
      (list
        (Instr 'movq (list (si-atom v) (Reg 'r11)))
        (Instr 'movq (list (Deref 'r11 0) (Reg 'rax)))
        (Instr 'sarq (list (Imm 1) (Reg 'rax)))
        (Instr 'andq (list (Imm 63) (Reg 'rax)))
        (Instr 'movq (list (Reg 'rax) x)))]
     [((Assign x (Allocate n (list 'Vector elem-types ...))))
      (list
        (Instr 'movq (list (Global 'free_ptr) (Reg 'r11)))
        (Instr 'addq (list (Imm (vector-offset n)) (Global 'free_ptr)))
        (Instr 'movq (list (Imm (vector-tag elem-types)) (Deref 'r11 0)))
        (Instr 'movq (list (Reg 'r11) x)))]
     [((Collect n))
      (list
        (Instr 'movq (list (Reg 'r15) (Reg 'rdi)))
        (Instr 'movq (list (Imm n) (Reg 'rsi)))
        (Callq 'collect 2))]
     [((Prim 'vector-set! (list v (Int n) e)))
      (list
        (Instr 'movq (list (si-atom v) (Reg 'r11)))
        (Instr 'movq (list (si-atom e) (Deref 'r11 (vector-offset n)))))]
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
     [((TailCall f args))
      (append
        (for/list ([a args] [r argument-passing-registers])
          (Instr 'movq (list (si-atom a) r)))
        (list
          (TailJmp (si-atom f) (length args))))]
     [((Goto label)) (list (Jmp label))]
     [((IfStmt (Prim op (list a b)) (Goto then-label) (Goto else-label)))
      (list
        (Instr 'cmpq (list (si-atom b) (si-atom a)))
        (JmpIf (dict-ref cmp->cc op) then-label)
        (Jmp else-label))]
     [((Return e)) (append (si-stmt (Assign (Reg 'rax) e)) (list (Jmp (symbol-append name 'conclusion))))]
     [((Seq stmt tail)) (append (si-stmt stmt) (si-tail tail))])
   (define copy-arguments
     (for/list ([p params] [r argument-passing-registers])
       (Instr 'movq (list r (Var (car p))))))
   (Def name '() 'Integer
     (dict-set* info 'num-root-spills 0 'num-params (length params))
     (hash-map/copy blocks (lambda (label block)
       (values label (Block '()
         (if (eq? label (symbol-append name 'start))
           (append copy-arguments (si-tail block))
           (si-tail block)))))))])
           

(define/match (select-instructions p)
  [((ProgramDefs info defs))
   (ProgramDefs info (map select-instructions-Def defs))])

;; uncover-live : x86Var -> x86Var
(define/match (location? atom)
  [((or (Reg _) (Var _))) #t]
  [(_) #f])

(define caller-saved-registers (map Reg '(rax rcx rdx rsi rdi r8 r9 r10 r11)))

(define (locations-written instr)
  (set-filter location? (match instr
    [(Instr (or 'addq 'subq 'xorq 'movq 'movzbq 'andq 'sarq 'leaq) (list _ b)) (set b)]
    [(Instr (or 'negq 'pushq 'popq) (list a)) (set a)]
    [(Instr 'set (list _ a)) (set a)]
    [(Instr 'cmpq _) (set)]
    [(Callq _ arity) (list->set caller-saved-registers)]
    [(IndirectCallq _ arity) (list->set caller-saved-registers)]
    [(Retq) (set (Reg 'rax))]
    [(or (Jmp _) (JmpIf _ _) (TailJmp _ _)) (set)]
    [_ (error 'locations-written "unhandled case: ~a" (Instr-name instr))])))

(define (enlarge-reg reg)
  (Reg (match (Reg-name reg)
    [(or 'ah 'al) 'rax]
    [(or 'bh 'bl) 'rbx]
    [(or 'ch 'cl) 'rcx]
    [(or 'dh 'dl) 'rdx])))

(define/match (uncover-live-Def def)
  [((Def name '() 'Integer info blocks))
   (define (arity-to-regs n)
     (list->set (take argument-passing-registers (min n 6))))
   (define (locations-read instr)
     (set-filter location? (match instr
       [(Instr (or 'addq 'subq 'xorq 'cmpq 'negq 'andq 'sarq) args) (list->set args)]
       [(Instr (or 'movq 'leaq) (list a _)) (set a)]
       [(Instr 'movzbq (list a _)) (set (enlarge-reg a))]
       [(Instr (or 'pushq 'popq) _) (set)]
       [(Callq _ arity) (arity-to-regs arity)]
       [(IndirectCallq f arity) (set-add (arity-to-regs arity) f)]
       [(TailJmp f arity) (set-add (arity-to-regs arity) f)]
       [(Retq) (set (Reg 'rax))]
       [_ (error 'locations-read "unhandled case: ~a" (Instr-name instr))])))
   (define (step live-after instr)
     (match instr
       [(or (Jmp _) (JmpIf _ _)) live-after]
       [(TailJmp _ _) (locations-read instr)]
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
   (Def name '() 'Integer info
     (hash-map/copy blocks (lambda (label block)
       (values label (Block (dict-set (Block-info block) 'live-afters (dict-ref label->live-afters label)) (Block-instr* block))))))])

(define/match (uncover-live p)
  [((ProgramDefs info defs))
   (ProgramDefs info (map uncover-live-Def defs))])

(define/match (build-interference-Def p)
  [((Def name '() 'Integer info blocks))
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
              (add-edge! gr v d)))])
       (when (or (Callq? instr) (IndirectCallq? instr))
         (define locals-types (dict-ref info 'locals-types))
         (for ([v live-set] #:when (and (Var? v) (dict-has-key? locals-types (Var-name v)) (Vector? (dict-ref locals-types (Var-name v)))))
           (for ([r callee-saved-registers])
             (add-edge! gr v r))))))
   (for ([(label block) (in-dict blocks)])
     (update-graph (dict-ref (Block-info block) 'live-afters) (Block-instr* block)))
   (Def name '() 'Integer (dict-set info 'conflicts gr) blocks)])

(define/match (build-interference p)
  [((ProgramDefs info defs))
   (ProgramDefs info (map build-interference-Def defs))])

(define callee-saved-registers (map Reg '(rbx rsp rbp r12 r13 r14 r15)))

(define/match (allocate-registers-Def def)
  [((Def name '() 'Integer info blocks))
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
   (define variables (map (lambda (p) (Var (car p))) (dict-ref info 'locals-types)))
   (define interference (dict-ref info 'conflicts))
   (define location->color (make-hash (map (lambda (p) (cons (cdr p) (car p))) color->reg)))
   (struct Sat (location forbids))
   (define queue (make-pqueue (lambda (a b) (>= (set-count (Sat-forbids a)) (set-count (Sat-forbids b))))))
   (define variable->handle (make-hash))
   (define (get-saturation v)
     (list->set (concat (for/list ([u (in-neighbors interference v)])
       (if (dict-has-key? location->color u)
         (list (dict-ref location->color u))
         '())))))
   (define (greedy-color forbids)
     (sequence-ref (sequence-filter (lambda (n) (not (set-member? forbids n))) (in-naturals 0)) 0))
   (for ([v variables])
     (let ([hdl (pqueue-push! queue (Sat v (get-saturation v)))])
       (dict-set! variable->handle v hdl)))
   (for ([i (in-range (pqueue-count queue))])
     (let* ([v (pqueue-pop! queue)]
            [c (greedy-color (Sat-forbids v))])
       (dict-set! location->color (Sat-location v) c)
       (for ([u (in-neighbors interference (Sat-location v))]
              #:when (Var? u))
         (let ([hdl (dict-ref variable->handle u)])
           (set-node-key! hdl (Sat u (get-saturation u)))
           (pqueue-decrease-key! queue hdl)))))
   (define num-regs 11)
   (define locals-types (dict-ref info 'locals-types))
   (define-values (variable->reg variable->stack variable->root)
     (let-values ([(reg-variables stack-variables root-variables)
                   (for/fold ([reg-variables '()] [stack-variables '()] [root-variables '()])
                             ([(location color) (in-dict location->color)])
                     (if (>= color num-regs)
                       (if (Vector? (dict-ref locals-types (Var-name location)))
                         (values reg-variables stack-variables (cons (cons location color) root-variables))
                         (values reg-variables (cons (cons location color) stack-variables) root-variables))
                       (values (cons (cons location color) reg-variables) stack-variables root-variables)))])
       (values
         (make-immutable-hash (for/list ([p reg-variables] #:when (Var? (car p))) (cons (car p) (dict-ref color->reg (cdr p)))))
         (make-immutable-hash (for/list ([p stack-variables] [i (in-naturals)]) (cons (car p) (Deref 'rbp (* -8 (+ 1 i))))))
         (make-immutable-hash (for/list ([p root-variables] [i (in-naturals)]) (cons (car p) (Deref 'r15 (* -8 (+ 1 i)))))))))
   ; (displayln "==============ATTENTION===============")
   ; (printf "~a ~a ~a\n" variable->reg variable->stack variable->root)
   ; (displayln (graphviz interference))
   (define (transform-instr instr)
     (define/match (transform-arg arg)
       [((Var x))
        (cond
          [(dict-has-key? variable->reg arg) (dict-ref variable->reg arg)]
          [(dict-has-key? variable->stack arg) (dict-ref variable->stack arg)]
          [(dict-has-key? variable->root arg) (dict-ref variable->root arg)])]
       [(_) arg])
     (match instr
       [(Instr op args) (Instr op (map transform-arg args))]
       [(IndirectCallq f arity) (IndirectCallq (transform-arg f) arity)]
       [(TailJmp f arity) (TailJmp (transform-arg f) arity)]
       [_ instr]))
   (define used-callee-saved-registers
     (set-intersect (list->set callee-saved-registers) (list->set (dict-values variable->reg))))
   (define stack-variables-size (* 8 (dict-count variable->stack)))
   (define new-info (list
     'num-root-spills (dict-count variable->root)
     'used-callee-saved-registers used-callee-saved-registers
     'stack-variables-size stack-variables-size))
   (Def name '() 'Integer (apply dict-set* info new-info)
     (hash-map/copy blocks (lambda (label block)
       (values label (Block (Block-info block) (map transform-instr (Block-instr* block)))))))])

(define/match (allocate-registers p)
  [((ProgramDefs info defs))
   (ProgramDefs info (map allocate-registers-Def defs))])

;; patch-instructions : psuedo-x86 -> x86
(define/match (patch-instructions-Def def)
  [((Def name '() 'Integer info blocks))
   (define/match (patch instr)
     [((Instr 'leaq (list a b))) #:when (not (Reg? b))
      (list
        (Instr 'leaq (list a (Reg 'rax)))
        (Instr 'leaq (list (Reg 'rax) b)))]
     [((TailJmp a arity)) #:when (not (eq? a (Reg 'rax)))
      (list
        (Instr 'movq (list a (Reg 'rax)))
        (TailJmp (Reg 'rax) arity))]
     [((Instr (or 'movq 'movzbq) (list a b))) #:when (equal? a b)
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
   (Def name '() 'Integer info (hash-map/copy blocks (lambda (label block)
     (values label (Block (Block-info block) (concat (map patch (Block-instr* block))))))))])

(define/match (patch-instructions p)
  [((ProgramDefs info defs))
   (ProgramDefs info (map patch-instructions-Def defs))])

;; prelude-and-conclusion : x86 -> x86
(define/match (prelude-and-conclusion-Def p)
  [((Def name '() 'Integer info blocks))
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
   (define initialize-root-stack
     (concat
       (for/list ([i (in-range (dict-ref info 'num-root-spills))])
         (list
           (Instr 'movq (list (Imm 0) (Deref 'r15 0)))
           (Instr 'addq (list (Imm 8) (Reg 'r15)))))))
   (define finalize-root-stack
     (let ([root-size (* 8 (dict-ref info 'num-root-spills))])
       (if (> root-size 0)
         (list (Instr 'subq (list (Imm root-size) (Reg 'r15))))
         '())))
   (define initialize-gc
     (list
       (Instr 'movq (list (Imm 65536) (Reg 'rdi)))
       (Instr 'movq (list (Imm 65536) (Reg 'rsi)))
       (Callq 'initialize 2)
       (Instr 'movq (list (Global 'rootstack_begin) (Reg 'r15)))))
   (define allocate-stack-variables
     (if (> stack-size 0) (list (Instr 'subq (list (Imm stack-size) (Reg 'rsp)))) '()))
   (define deallocate-stack-variables
     (if (> stack-size 0) (list (Instr 'addq (list (Imm stack-size) (Reg 'rsp)))) '()))
   (define/match (transform-instr instr)
     [((TailJmp f arity))
      `(
        ,@finalize-root-stack
        ,@restore-registers
        ,@deallocate-stack-variables
        ,(Instr 'popq (list (Reg 'rbp)))
        ,(IndirectJmp f))]
     [(_) (list instr)])
   (set! blocks
     (for/hash ([(label block) (in-dict blocks)])
       (match block
         [(Block info instrs) (values label (Block info (concat (map transform-instr instrs))))])))
   ;(Def name '() 'Integer info (dict-set* blocks
   (dict-set* blocks
     name (Block '() `(
       ,(Instr 'pushq (list (Reg 'rbp)))
       ,(Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))
       ,@allocate-stack-variables
       ,@save-registers
       ,@(if (eq? name 'main) initialize-gc '())
       ,@initialize-root-stack
       ,(Jmp (symbol-append name 'start))))
     (symbol-append name 'conclusion) (Block '() `(
       ,@finalize-root-stack
       ,@restore-registers
       ,@deallocate-stack-variables
       ,(Instr 'popq (list (Reg 'rbp)))
       ,(Retq))))])

(define/match (prelude-and-conclusion p)
  [((ProgramDefs info defs))
   ;(ProgramDefs info (map prelude-and-conclusion-Def defs))])
   (X86Program info (apply hash-union (map prelude-and-conclusion-Def defs)))])
  
;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( ("shrink" ,shrink ,interp-Lfun ,type-check-Lfun)
     ("uniquify" ,uniquify ,interp-Lfun ,type-check-Lfun)
     ("reveal FunRef" ,reveal-functions ,interp-Lfun-prime ,type-check-Lfun)
     ("limit funtion parameters" ,limit-functions ,interp-Lfun-prime ,type-check-Lfun)
     ("elaborate" ,type-check-Lfun ,interp-Lfun-prime ,type-check-Lfun)
     ("expose allocation" ,expose-allocation ,interp-Lfun-prime ,type-check-Lfun)
     ("uncover get!" ,uncover-get! ,interp-Lfun-prime ,type-check-Lfun)
     ("remove complex operands" ,remove-complex-operands ,interp-Lfun-prime ,type-check-Lfun)
     ("explicate control" ,explicate-control ,interp-Cfun ,type-check-Cfun)
     ("instruction selection" ,select-instructions ,interp-x86-3)
     ("liveness analysis" ,uncover-live ,interp-x86-3)
     ("build interference graph" ,build-interference ,interp-x86-3)
     ("allocate registers" ,allocate-registers ,interp-x86-3)
     ("patch instructions" ,patch-instructions ,interp-x86-3)
     ("prelude and conclusion" ,prelude-and-conclusion #f)
     ))

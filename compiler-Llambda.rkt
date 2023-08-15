#! /usr/bin/env -S nix shell nixpkgs#racket --command racket
#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Llambda.rkt")
(require "interp-Llambda-prime.rkt")
(require "interp-Clambda.rkt")
(require "type-check-Llambda.rkt")
(require "type-check-Clambda.rkt")
(require "utilities.rkt")
(require "interp-SSA.rkt")
(require "interp.rkt")
(require graph)
(require "priority_queue.rkt")
(require "multigraph.rkt")
(require data/queue)
(provide (all-defined-out))

(define compiler-Llambda
  (class object%
    (super-new)

    (define/public (concat lsts) (apply append lsts))
   
    (define/public (set-filter p s) (list->set (filter p (set->list s))))

    (define/public (append-point sym) (symbol-append sym (string->symbol ".")))

    (define/public (gc-type? type)
      (match type
        [(list 'Vector _ ...) #t]
        [_ #f]))

    (define/public (hash-remove* h keys)
      (for/fold ([r h]) ([k keys])
        (hash-remove r k)))
         
    (define/public (let-bindings bindings exp)
      (for/foldr ([exp exp]) ([binding bindings])
        (Let (car binding) (cdr binding) exp)))

    (define/public ((induct-L f) e)
      (match e
        [(Lambda params rty body) (f (Lambda params rty ((induct-L f) body)))]
        [(or (Int _) (Var _) (Bool _) (Void) (GetBang _) (Collect _) (Allocate _ _) (GlobalValue _) (FunRef _ _) (AllocateClosure _ _ _)) (f e)]
        [(Prim op args) (f (Prim op (map (induct-L f) args)))]
        [(Let x e body) (f (Let x ((induct-L f) e) ((induct-L f) body)))]
        [(If c t e) (f (If ((induct-L f) c) ((induct-L f) t) ((induct-L f) e)))]
        [(SetBang x e) (f (SetBang x ((induct-L f) e)))]
        [(Begin effs e) (f (Begin (map (induct-L f) effs) ((induct-L f) e)))]
        [(WhileLoop c e) (f (WhileLoop ((induct-L f) c) ((induct-L f) e)))]
        [(HasType e t) (f (HasType ((induct-L f) e) t))]
        [(Apply e es) (f (Apply ((induct-L f) e) (map (induct-L f) es)))]
        [(Closure arity exps) (f (Closure arity (map (induct-L f) exps)))]))

    (define/public (subexpressions exp)
      (match exp
        [(or (Void) (Bool _) (Var _) (Int _) (GetBang _) (Collect _) (Allocate _ _) (GlobalValue _) (FunRef _ _) (AllocateClosure _ _ _)) '()]
        [(Apply e es) (cons e es)]
        [(SetBang _ e) (list e)]
        [(Begin effs e) (append effs (list e))]
        [(WhileLoop c e) (list c e)]
        [(If c t e) (list c t e)]
        [(Let _ e body) (list e body)]
        [(Prim _ args) args]
        [(Lambda _ _ body) (list body)]
        [(HasType e _) (list e)]
        [(Closure _ es) es]))
      
    (define/public (analyse-dataflow cfg transfer bottom join)
      (define label->value (make-hash))
      (define work-list (make-queue))
      (for ([v (in-vertices cfg)])
        (dict-set! label->value v bottom)
        (enqueue! work-list v))
      (define cfg-t (transpose cfg))
      (while (not (queue-empty? work-list))
        (define curr-node (dequeue! work-list))
        (define input
          (join
            (for/fold ([args'()]) ([pred (in-neighbors cfg-t curr-node)])
              (cons (dict-ref label->value pred) args))))
        (define output (transfer curr-node input))
        (when (not (equal? output (dict-ref label->value curr-node)))
          (dict-set! label->value curr-node output)
          (for ([succ (in-vertices cfg)])
            (enqueue! work-list succ))))
      label->value)

    (define/public (shrink-exp-induct exp)
      (match exp
        [(Prim 'and (list a b)) (If a b (Bool #f))]
        [(Prim 'or (list a b)) (If a (Bool #t) b)]
        [exp exp]))
         
    (define/public (pass-shrink p)
      (define shrink-exp (induct-L (lambda (x) (shrink-exp-induct x))))
 
      (define/match (shrink-Def def)
        [((Def name params rty info body))
         (Def name params rty info (shrink-exp body))])
 
      (match p
        [(Program info exp)
         (pass-shrink (ProgramDefsExp info '() exp))]
        [(ProgramDefsExp info defs exp)
         (ProgramDefs info (append (map shrink-Def defs) (list (shrink-Def (Def 'main '() 'Integer (hash) exp)))))]))
      
    (define/public (uniquify-exp env)
      (match-lambda
        [(Lambda params rty body)
         (define new-env
           (for/fold ([new-env env]) ([p params])
             (dict-set new-env (car p) (gensym (append-point (car p))))))
         (Lambda
           (for/list ([p params])
             (match p
               [`(,x : ,t) `(,(dict-ref new-env x) : ,t)]))
           rty
           ((uniquify-exp new-env) body))]
        [(HasType e t) (HasType ((uniquify-exp env) e) t)]
        [(Apply f args) (Apply ((uniquify-exp env) f) (map (uniquify-exp env) args))]
        [(and exp (or (Void) (Int _) (Bool _))) exp]
        [(SetBang x e) (SetBang (dict-ref env x) ((uniquify-exp env) e))]
        [(Begin effs e) (Begin (map (uniquify-exp env) effs) ((uniquify-exp env) e))]
        [(WhileLoop c e) (WhileLoop ((uniquify-exp env) c) ((uniquify-exp env) e))]
        [(Var x)
         (Var (dict-ref env x))]
        [(Let x e body)
         (let ([new-x (gensym (append-point x))])
           (Let new-x ((uniquify-exp env) e) ((uniquify-exp (dict-set env x new-x)) body)))]
        [(Prim op es)
         (Prim op (for/list ([e es]) ((uniquify-exp env) e)))]
        [(If c t e) (If ((uniquify-exp env) c) ((uniquify-exp env) t) ((uniquify-exp env) e))]))

    (define/public (pass-uniquify p)
      (match p
        [(ProgramDefs info defs)
   
         (define env
           (for/hash ([def defs])
             (values (Def-name def) (Def-name def))))
   
         (ProgramDefs info
           (for/list ([def defs])
             (match def
               [(Def name params rty info body)
                (define new-env
                  (for/fold ([new-env env]) ([p params])
                    (dict-set new-env (car p) (gensym (append-point (car p))))))
                (Def
                  name
                  (for/list ([p params])
                    (match p
                      [`(,x : ,t) `(,(dict-ref new-env x) : ,t)]))
                  rty
                  info
                  ((uniquify-exp new-env) body))])))]))

    (define/public (pass-reveal-functions p)
      (match p
        [(ProgramDefs info defs)
   
         (define fun->arity
           (for/hash ([def defs])
             (values (Def-name def) (length (Def-param* def)))))
   
         (define reveal-functions-exp
           (induct-L
             (match-lambda
               [(Var x)
                #:when (dict-has-key? fun->arity x)
                (FunRef x (dict-ref fun->arity x))]
               [exp exp])))
   
         (ProgramDefs info
           (for/list ([def defs])
             (match def
               [(Def name params rty info body)
                (Def name params rty info (reveal-functions-exp body))])))]))

    (define/public (free-variables exp)
      (match exp
        [(Var x) (set x)]
        [(Let x e body) (set-union (free-variables e) (set-subtract (free-variables body) (set x)))]
        [(Lambda params _ body) (set-subtract (free-variables body) (list->set (map car params)))]
        [(SetBang x e) (set-union (set x) (free-variables e))]
        [_ (apply set-union (set) (map (lambda (x) (free-variables x)) (subexpressions exp)))]))

    (define/public (convert-assignments-induct captured)
      (match-lambda
        [(Let x e body)
         #:when (set-member? captured x)
         (Let x (Prim 'vector (list e)) body)]
        [(Var x)
         #:when (set-member? captured x)
         (Prim 'vector-ref (list (Var x) (Int 0)))]
        [(SetBang x e)
         #:when (set-member? captured x)
         (Prim 'vector-set! (list (Var x) (Int 0) e))]
        [(Lambda params rty body)
         (define boxed-params
           (for/hash ([p params]
                      #:when (set-member? captured (car p)))
             (values (car p) (gensym (append-point (car p))))))
         (define new-params 
           (for/list ([p params])
             (match p
               [(list x ': t) (list (dict-ref boxed-params x x) ': t)])))
         (Lambda new-params rty
           (for/foldr ([new-body body]) ([(p renamed) (in-dict boxed-params)])
             (Let p (Prim 'vector (list (Var renamed))) new-body)))]
        [exp exp]))

    (define/public (pass-convert-assignments p)
      (define/match (convert-assignments-Def def)
        [((Def name params rty info body))
      
         (define/match (captured-by-lambda exp)
           [((Lambda params _ body)) (set-union (captured-by-lambda body) (set-subtract (free-variables body) (list->set (map car params))))]
           [(_) (apply set-union (set) (map captured-by-lambda (subexpressions exp)))])
        
         (define captured (captured-by-lambda body))
         (define boxed-params
           (for/hash ([p params]
                      #:when (set-member? captured (car p)))
             (values (car p) (gensym (append-point (car p))))))
      
         (define new-params 
           (for/list ([p params])
             (match p
               [(list x ': t) (list (dict-ref boxed-params x x) ': t)])))
      
         (Def name new-params rty info
           (for/foldr ([new-body ((induct-L (convert-assignments-induct captured)) body)]) ([(p renamed) (in-dict boxed-params)])
             (Let p (Prim 'vector (list (Var renamed))) new-body)))])
      (match p
        [(ProgramDefs info defs)
         (ProgramDefs info (map convert-assignments-Def defs))]))
         
    (define/public (convert-closure-type type)
      (define (recur x) (convert-closure-type x))
      (match type
        [`(,arg-tys ... -> ,rty)
         `(Vector ((Vector _) ,@(map recur arg-tys) -> ,(recur rty)))]
        [`(Vector ,etys ...)
         `(Vector ,@(map recur etys))]
        [type type]))
         
    (define/public (pass-convert-closures p)
      (define lifted-defs '())
   
      (define (convert-params closure-var closure-type params)
        (cons (list closure-var ': closure-type)
          (for/list ([p params])
            (match p
              [(list x ': t) (list x ': (convert-closure-type t))]))))
   
      (define/match (lift-lambda lmd)
        [((Lambda params rty body))
         (define (sorted-free-variables exp)
           (sort (set->list (free-variables exp)) symbol<?)) 
      
         (define fvs (sorted-free-variables lmd))
      
         (define/match (free-variables->type exp)
           [((HasType (Var x) t)) (hash x t)]
           [((Lambda params _ body)) (hash-remove* (free-variables->type body) (map car params))]
           [((Let x e body)) (hash-union (free-variables->type e) (hash-remove (free-variables->type body) x))]
           [(_) (apply hash-union (hash) (map free-variables->type (subexpressions exp)))])
      
         (define fv->type-dict (free-variables->type lmd))
         (define (fv->type t)
           (convert-closure-type (dict-ref fv->type-dict t)))
         (define closure-type `(Vector _ ,@(for/list ([v fvs]) (fv->type v))))
         (define closure-var (gensym 'closure.))
         (define lambda-name (gensym 'lambda.))
      
         (define new-body
           (for/foldr ([new-body body]) ([fv fvs] [n (in-naturals)])
             (Let fv (Prim 'vector-ref (list (Var closure-var) (Int (+ 1 n)))) new-body)))
      
         (set! lifted-defs
           (cons (Def lambda-name (convert-params closure-var closure-type params) (convert-closure-type rty) '() new-body)
                 lifted-defs))
      
         (define arity (length params))
         (Closure arity (cons (FunRef lambda-name arity) (for/list ([v fvs]) (Var v))))])
   
      (define convert-exp
        (induct-L
          (match-lambda
            [(Lambda params rty body) (lift-lambda (Lambda params rty body))]
            [(FunRef name arity) (Closure arity (list (FunRef name arity)))]
            [(Apply f args)
             (define closure-var (gensym 'closure.))
             (Let closure-var f
               (Apply (Prim 'vector-ref (list (Var closure-var) (Int 0))) (cons (Var closure-var) args)))]
            [exp exp])))
   
      (define/match (convert-Def def)
        [((Def name params rty info body))
         (define new-params
           (if (equal? name 'main)
             (for/list ([p params])
               (match p
                 [(list x ': t) (list x ': (convert-closure-type t))]))
             (convert-params (gensym 'closure.) '(Vector _) params)))
         (Def name new-params (convert-closure-type rty) info (convert-exp body))])
      
      (match p
        [(ProgramDefs info defs)
         (ProgramDefs info (append (map convert-Def defs) lifted-defs))]))
  
    (define/public (pass-limit-functions p)
      (define convert-calls
        (induct-L
          (match-lambda
            [(Apply e es)
             #:when (> (length es) 6)
             (Apply e (append (take es 5) (list (Prim 'vector (drop es 5)))))]
            [exp exp])))
   
      (define/match (limit-functions-Def def)
        [((Def name params rty info body))
         (define new-body (convert-calls body))
         (when (> (length params) 6)
           (define rest-names (map car (drop params 5)))
           (define rest-types (map caddr (drop params 5)))
           (define rest-var (gensym 'rest-params.))
           (set! params (append (take params 5) (list (list rest-var ': (cons 'Vector rest-types)))))
           (define rename-rest
             (induct-L
               (match-lambda
                 [(Var x)
                  #:when (set-member? rest-names x)
                  (Prim 'vector-ref (list (Var rest-var) (Int (index-of rest-names x))))]
                 [exp exp])))
           (set! new-body (rename-rest new-body)))
         (Def name params rty info new-body)])
     
      (match p
        [(ProgramDefs info defs)
         (ProgramDefs info (map limit-functions-Def defs))]))

    (define/public (pass-expose-allocation p)
      (define expose-allocation-exp
        (induct-L
          (match-lambda
            [(HasType (Prim 'vector es) type)
          
             (define (eval-elems es xs body)
               (for/foldr ([exp body]) ([x xs] [e es])
                 (Let x e exp)))
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
        
            [(HasType (Closure arity es) type)
          
             (define (eval-elems es xs body)
               (for/foldr ([exp body]) ([x xs] [e es])
                 (Let x e exp)))
             (define n (length es))
             (define allocation-size (* 8 (+ 1 n)))
             (define check-enough-space
               (If (Prim '< (list (Prim '+ (list (GlobalValue 'free_ptr) (Int allocation-size)))
                                  (GlobalValue 'fromspace_end)))
                 (Void)
                 (Collect allocation-size)))
             (define closure-var (gensym 'closure.))
             (define elems-vars
               (for/list ([i (in-range n)])
                 (gensym (symbol-append 'closure.elem. (append-point (string->symbol (number->string i)))))))
          
             (eval-elems es elems-vars
               (Begin (list check-enough-space)
                 (Let closure-var (AllocateClosure n type arity)
                   (Begin (for/list ([i (in-range n)] [v elems-vars]) (Prim 'vector-set! (list (Var closure-var) (Int i) (Var v))))
                     (Var closure-var)))))]
        
            [exp exp])))
   
      (match p
        [(ProgramDefs info defs)
         (ProgramDefs info
           (for/list ([def defs])
             (match def
               [(Def name params rty info body)
                (Def name params rty info (expose-allocation-exp body))])))]))

    (define/public (pass-uncover-get! p)
      (define/match (collect-set! exp)
        [((SetBang x e)) (set-union (set x) (collect-set! e))]
        [(_) (apply set-union (set) (map collect-set! (subexpressions exp)))])
   
      (define uncover-get!-exp
        (induct-L
          (match-lambda
            [(Prim op args)
             (let ([muts (apply set-union (set) (map collect-set! args))])
               (Prim op
                 (for/list ([arg args])
                   (match arg
                     [(Var x)
                      #:when (set-member? muts x)
                      (GetBang x)]
                     [_ arg]))))]
            [exp exp])))
   
      (match p
        [(ProgramDefs info defs)
         (ProgramDefs info
           (for/list ([def defs])
             (match def
               [(Def name params rty info body)
                (Def name params rty info (uncover-get!-exp body))])))]))
   
    (define/public (complex-exp? e)
      (match e
        [(Begin _ _) (gensym 'begin.)]
        [(If _ _ _) (gensym 'if.)]
        [(Let _ _ _) (gensym 'let.)]
        [(WhileLoop _ _) (gensym 'while.)]
        [(SetBang _ _) (gensym 'set!.)]
        [(Prim op _) (gensym (symbol-append 'op. (append-point op)))]
        [(Collect _) (gensym 'collect.)]
        [(Allocate _ _) (gensym 'allocate.)]
        [(GlobalValue x) (gensym (append-point x))]
        [(FunRef _ _) (gensym 'fun-ref.)]
        [(AllocateClosure _ _ _) (gensym 'allocate-closure.)]
        [(Apply _ _) (gensym 'apply.)]
        [(GetBang x) (gensym (append-point x))]
        [_ #f]))
         
    (define/public (remove-complex-operands-exp-induct exp)
      (match exp
        [(Prim op args)
         (define-values (bindings atoms)
           (for/fold ([bindings '()] [atoms '()]) ([exp args])
             (let-values ([(bs a) (remove-complex-operands-atom exp)])
               (values (append bindings bs) (append atoms (list a))))))
         (let-bindings bindings (Prim op atoms))]
        [(Apply f args)
         (define-values (bindings atoms)
           (for/fold ([bindings '()] [atoms '()]) ([exp (cons f args)])
             (let-values ([(bs a) (remove-complex-operands-atom exp)])
               (values (append bindings bs) (append atoms (list a))))))
         (let-bindings bindings (Apply (car atoms) (cdr atoms)))]
        [e e]))
         
    (define/public (remove-complex-operands-exp exp)
      ((induct-L (lambda (x) (remove-complex-operands-exp-induct x))) exp))
   
    (define/public (remove-complex-operands-atom e)
      (define var (complex-exp? e))
      (define remove-get
        (match-lambda
          [(GetBang x) (Var x)]
          [exp exp]))
      (if (equal? var #f)
        (values '() e)
        (values (list (cons var (remove-get e))) (Var var))))
         
    (define/public (pass-remove-complex-operands p)
      (match p
        [(ProgramDefs info defs)
         (ProgramDefs info
           (for/list ([def defs])
             (match def
               [(Def name params rty info body)
                (Def name params rty info (remove-complex-operands-exp body))])))]))
         
    (define blocks (make-hash))
         
    (define/public (emit-named-block label block)
      (dict-set! blocks label block)
      (Goto label))
         
    (define/public (emit-block hint block)
      (if (Goto? block)
        block
        (emit-named-block (gensym hint) block)))

    (define/public (explicate-effects effs cont)
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
        [(cons (or (Prim _ _) (Int _) (Var _) (Bool _) (Void) (GlobalValue _) (Allocate _ _) (FunRef _ _) (AllocateClosure _ _ _)) effs)
         (explicate-effects effs cont)]
        [(cons (If c t e) effs)
         (let ([cont (emit-block 'effs. (explicate-effects effs cont))])
           (explicate-if c (explicate-effects (list t) cont) (explicate-effects (list e) cont)))]
        [(cons (Let x e body) effs)
         (explicate-assign x e (explicate-effects (cons body effs) cont))]))
            
    (define/public (explicate-if c t e)
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
        [(Prim op args)
         #:when (set-member? '(eq? < <= > >=) op)
         (IfStmt c (emit-block 'then. t) (emit-block 'else. e))]
        [(If c2 t2 e2)
         (let ([goto-t (emit-block 'then. t)]
               [goto-e (emit-block 'else. e)])
           (explicate-if c2 (explicate-if t2 goto-t goto-e) (explicate-if e2 goto-t goto-e)))]
        [(Let x ee body)
         (explicate-assign x ee (explicate-if body t e))]
        [_ (error 'explicate-if "~a is not a predicate" c)]))
      
    (define/public (explicate-assign x e cont)
      (match e
        [(Apply f args) (Seq (Assign (Var x) (Call f args)) cont)]
        [(or (Collect _) (SetBang _ _) (WhileLoop _ _))
         (explicate-effects (list e) (explicate-assign x (Void) cont))]
        [(GetBang _) (error 'explicate-assign "impossible")]
        [(Begin effs e) (explicate-effects effs (explicate-assign x e cont))]
        [(If c t e)
         (let ([goto-cont (emit-block 'let.body. cont)])
           (explicate-if c (explicate-assign x t goto-cont) (explicate-assign x e goto-cont)))]
        [(Let x2 e2 body) (explicate-assign x2 e2 (explicate-assign x body cont))]
        [_ (Seq (Assign (Var x) e) cont)]))

    (define/public (explicate-tail e)
      (match e
        [(Apply f args) (TailCall f args)]
        [(or (Collect _) (SetBang _ _) (WhileLoop _ _))
         (explicate-effects (list e) (Return (Void)))]
        [(GetBang _) (error 'explicate-tail "impossible")]
        [(Begin effs e) (explicate-effects effs (explicate-tail e))]
        [(If c t e) (explicate-if c (explicate-tail t) (explicate-tail e))]
        [(Let x e body) (explicate-assign x e (explicate-tail body))]
        [_ (Return e)]))

    (define/public (pass-explicate-control p)
      (define/match (explicate-control-Def def)
        [((Def name params rty info body))
      
         (set! blocks (make-hash))
      
         (Def name params rty info
           (let ([start (explicate-tail body)])
             (emit-named-block (symbol-append name 'start) start)
             (make-immutable-hash (hash->list blocks))))])
   
      (match p
        [(ProgramDefs info defs)
         (ProgramDefs info (map explicate-control-Def defs))]))
         
    (define/public (pass-optimize-blocks p)
      (define/match (collect-jumps tail)
        [((Goto label))
         (set label)]
        [((IfStmt c (Goto a) (Goto b)))
         (set a b)]
        [((Seq s t))
         (collect-jumps t)]
        [(_)
         (set)])
      
      (define (remove-duplicate-blocks blocks)
        (define uniq->label
          (for/hash ([(label block) (in-dict blocks)])
            (values block label)))
        (define/match (rewrite-jumps tail)
          [((Goto label))
           (Goto (dict-ref uniq->label (dict-ref blocks label)))]
          [((IfStmt c g1 g2))
           (IfStmt c (rewrite-jumps g1) (rewrite-jumps g2))]
          [((Seq s t))
           (Seq s (rewrite-jumps t))]
          [(s) s])
        (for/hash ([(label tail) (in-dict blocks)])
          (values label (rewrite-jumps tail))))
        
      (define (remove-dead-blocks defname blocks)
        (define alive (set))
        (define frontier (set (symbol-append defname 'start)))
        (while (not (set-empty? frontier))
          (set! alive (set-union alive frontier))
          (set! frontier
            (set-subtract
              (for/fold ([frontier (set)]) ([label (in-set frontier)])
                (set-union frontier (collect-jumps (dict-ref blocks label))))
              alive)))
        (for/hash ([label (in-set alive)])
          (values label (dict-ref blocks label))))
        
      (define/match (optimize-blocks-Def def)
        [((Def name params rty info blocks))
         (Def name params rty info (remove-dead-blocks name (remove-duplicate-blocks blocks)))])
         
      (match p
        [(ProgramDefs info defs)
         (ProgramDefs info (map optimize-blocks-Def defs))]))
      
    (define/public (select-instructions-atom atom)
      (match atom
        [(Int i) (Int i)]
        [(Bool b) (if b (Int 1) (Int 0))]
        [(Var x) (Var x)]
        [(Void) (Int 0)]))
           
    (define/public (select-instructions-stmt s)
      (define (vector-offset n) (* 8 (+ 1 n)))
      (define (vector-tag elem-types)
        (define pointer-mask
          (for/fold ([mask 0]) ([i (in-naturals)] [t elem-types])
            (bitwise-ior mask
              (match t
                [`(Vector ,_ ...) (arithmetic-shift 1 (+ 7 i))]
                [_ 0]))))
        (define vector-length (arithmetic-shift (length elem-types) 1))
        (bitwise-ior pointer-mask vector-length))

      (define/match (closure-tag closure-type)
        [(`(Vector ((Vector ,_ ...) ,arg-tys ... -> ,rty) ,capture-tys ...))
         (define arity (length arg-tys))
         (define elem-types (drop closure-type 1))
         (bitwise-ior (vector-tag elem-types)
           (arithmetic-shift arity 58))])

      (match s
        [(Assign (Var x) (GlobalValue name))
         (list
           (SsaInstr x 'load_global (list name)))]
        [(Assign (Var x) (FunRef name _))
         (list
           (SsaInstr x 'func_addr (list name)))]
        [(Assign (Var x) (Call f args))
         (list
           (SsaInstr x 'indirectcall (map (lambda (x) (select-instructions-atom x)) (cons f args))))]
        [(Assign (Var x) (Prim 'vector-ref (list v (Int n))))
         (list
           (SsaInstr x 'load (list (select-instructions-atom v) (Int (vector-offset n)))))]
        [(Assign (Var x) (Prim 'vector-set! (list v (Int n) e)))
         (list
           (Store (select-instructions-atom e) (select-instructions-atom v) (Int (vector-offset n)))
           (SsaInstr x 'id (list (Int 0))))]
        [(Assign (Var x) (Prim 'vector-length (list v)))
         (list
           (SsaInstr x 'load (list (select-instructions-atom v) (Int 0)))
           (SsaInstr x 'sar (list (Int 1) (Var x)))
           (SsaInstr x 'and (list (Int 63) (Var x))))]
        [(Assign (Var x) (Allocate n (list 'Vector elem-types ...)))
         (list
           (SsaInstr x 'allocate (list (Int (vector-offset n))))
           (Store (Int (vector-tag elem-types)) (Var x) (Int 0)))]
        [(Assign (Var x) (AllocateClosure n type arity))
         (list
           (SsaInstr x 'allocate (list (Int (vector-offset n))))
           (Store (Int (closure-tag type)) (Var x) (Int 0)))]
        [(Assign (Var x) (Prim 'procedure-arity (list c)))
         (list
           (SsaInstr x 'load (list (select-instructions-atom c) (Int 0)))
           (SsaInstr x 'sar (list (Int 58) (Var x)))
           (SsaInstr x 'and (list (Int 31) (Var x))))]
        [(Collect n)
         (list
           (Collect n))]
        [(Prim 'vector-set! (list v (Int n) e))
         (list
           (Store (select-instructions-atom e) (select-instructions-atom v) (Int (vector-offset n))))]
        [(Assign (Var x) (Prim 'read '()))
         (list (SsaInstr x 'call (list 'read_int)))]
        [(Assign (Var x) (Prim '- (list a)))
         (list (SsaInstr x 'neg (list (select-instructions-atom a))))]
        [(Assign (Var x) (Prim '- (list a b)))
         (list (SsaInstr x 'sub (list (select-instructions-atom a) (select-instructions-atom b))))]
        [(Assign (Var x) (Prim '+ (list a b)))
         (list (SsaInstr x 'add (list (select-instructions-atom a) (select-instructions-atom b))))]
        [(Assign (Var x) (Prim 'not (list a)))
         (list (SsaInstr x 'xor (list (Int 1) x)))]
        [(Assign (Var x) (Prim op (list a b)))
         #:when (set-member? '(eq? < <= > >=) op)
         (list (SsaInstr x 'cmp (list op (select-instructions-atom a) (select-instructions-atom b))))]
        [(Assign (Var x) atom) (list (SsaInstr x 'id (list (select-instructions-atom atom))))]
        [(Prim 'read '()) (list (SsaInstr (gensym 'unused.) 'call (list 'read_int)))]))
      
    (define/public (select-instructions-tail tail)
      (match tail
        [(TailCall f args)
         (list (TailCall (select-instructions-atom f) (map (lambda (x) (select-instructions-atom x)) args)))]
        [(Goto label) (list (Jmp label))]
        [(IfStmt (Prim op (list a b)) (Goto then-label) (Goto else-label))
         (list (Branch op (select-instructions-atom a) (select-instructions-atom b) then-label else-label))]
        [(Return e)
         (define var (gensym 'retval.))
         (append
          (select-instructions-stmt (Assign (Var var) e))
          (list (Return (Var var))))]
        [(Seq stmt tail) (append (select-instructions-stmt stmt) (select-instructions-tail tail))]))
      
    (define/public (pass-select-instructions p)
      (define/match (select-instructions-Def p)
        [((Def name params _ info blocks))
         (Def name (map car params) 'Integer info
           (for/hash ([(label tail) (in-dict blocks)])
             (values label (SsaBlock '() (select-instructions-tail tail)))))])
   
      (match p
        [(ProgramDefs info defs)
         (ProgramDefs info (map select-instructions-Def defs))]))
         
    (define/public (pass-build-dominance p)
      (define/match (build-dominance-Def def)
        [((Def name params 'Integer info blocks))
         (define cfg (directed-graph '()))
         (for ([(curr-label block) (in-dict blocks)])
           (add-vertex! cfg curr-label)
           (define (add! to)
             (assert "jumping outside function" (dict-has-key? blocks to))
             (add-vertex! cfg to)
             (add-directed-edge! cfg curr-label to))
           (for ([instr (SsaBlock-instr* block)])
             (match instr
               [(Jmp label)
                (add! label)]
               [(Branch _ _ _ then-label else-label)
                (add! then-label)
                (add! else-label)]
               [_ #f])))
         (define dominators
           (let ([bottom (list->set (get-vertices cfg))]
                 [join (lambda (args) (if (null? args) (set) (set-intersections args)))]
                 [transfer (lambda (curr input) (set-add input curr))])
             (analyse-dataflow cfg transfer bottom join)))
         (define dominatees
           (for*/fold ([dominatees (for/hash ([label (in-vertices cfg)]) (values label (set)))])
                      ([(to domed-by) (in-dict dominators)]
                       [from (in-set domed-by)])
             (dict-update dominatees from (lambda (ds) (set-add ds to)))))
         (define (strictly-dominates a b)
           (and (not (equal? a b))
                (set-member? (dict-ref dominatees a) b)))
         (define immediate-dominatees ; a i< b iff a < b && !\exists c. a < c && c < b
           (for*/fold ([immediate-dominatees (for/hash ([label (in-vertices cfg)]) (values label (set)))])
                      ([(a bs) (in-dict dominatees)]
                       [b (in-set bs)]
                       #:when (and (not (equal? a b))
                                   (empty? (filter (lambda (c) (and (not (equal? a c))
                                                                    (strictly-dominates c b)))
                                                   (set->list bs)))))
             (dict-update immediate-dominatees a (lambda (ids) (set-add ids b)))))
         (define dominance-frontiers ; a df b iff !(a < b) && \exists c. a <= c && c \in b.preds
           (for*/fold ([dominance-frontiers (for/hash ([label (in-vertices cfg)]) (values label (set)))])
                      ([(a cs) (in-dict dominatees)]
                       [c (in-set cs)]
                       [b (in-neighbors cfg c)]
                       #:when (not (and (not (equal? a b)) (set-member? cs b))))
             (dict-update dominance-frontiers a (lambda (df) (set-add df b)))))
         ; (printf "cfg:\n~a\n"
         ;   (graphviz cfg
         ;     #:vertex-attributes
         ;     (list
         ;       (list 'xlabel
         ;             (lambda (label) (format "~a" (dict-ref immediate-dominatees label)))))))
         (Def name params 'Integer
           (dict-set* info
             'control-flow-graph cfg
             'immediate-dominatees immediate-dominatees
             'dominance-frontiers dominance-frontiers)
           blocks)])
  
      (match p
        [(ProgramDefs info defs)
         (ProgramDefs info (map build-dominance-Def defs))]))

    (define/public (argument-passing-registers) (map Reg '(rdi rsi rdx rcx r8 r9)))
         
    (define cmp->cc
      '((eq? . e) (< . l) (<= . le) (> . g) (>= . ge)))
         
    (define/public (location? atom)
      (match atom
        [(or (Reg _) (Var _)) #t]
        [_ #f]))

    (define (caller-saved-registers) (map Reg '(rax rcx rdx rsi rdi r8 r9 r10 r11)))

    (define (callee-saved-registers) (map Reg '(rbx rsp rbp r12 r13 r14 r15)))
         
    (define/public (locations-written instr)
      (set-filter (lambda (x) (location? x))
        (match instr
          [(Instr (or 'addq 'subq 'xorq 'movq 'movzbq 'andq 'sarq 'leaq) (list _ b)) (set b)]
          [(Instr (or 'negq 'pushq 'popq) (list a)) (set a)]
          [(Instr 'set (list _ a)) (set (enlarge-reg a))]
          [(Instr 'cmpq _) (set)]
          [(Callq _ arity) (list->set (caller-saved-registers))]
          [(IndirectCallq _ arity) (list->set (caller-saved-registers))]
          [(Retq) (set (Reg 'rax))]
          [(or (Jmp _) (JmpIf _ _) (TailJmp _ _)) (set)])))
      
    (define/public (locations-read instr)
      (define (arity-to-regs n)
        (list->set (take (argument-passing-registers) (min n 6))))
      (set-filter (lambda (x) (location? x))
        (match instr
          [(Instr (or 'addq 'subq 'xorq 'cmpq 'negq 'andq 'sarq) args) (list->set args)]
          [(Instr (or 'movq 'leaq) (list a _)) (set a)]
          [(Instr 'movzbq (list a _)) (set (enlarge-reg a))]
          [(Instr (or 'pushq 'popq 'set) _) (set)]
          [(Callq _ arity) (arity-to-regs arity)]
          [(IndirectCallq f arity) (set-add (arity-to-regs arity) f)]
          [(TailJmp f arity) (set-add (arity-to-regs arity) f)]
          [(Retq) (set (Reg 'rax))]
          [_ (error 'locations-read "unhandled case: ~a" (Instr-name instr))])))

    (define/public (enlarge-reg arg)
      (match arg
        [(ByteReg (or 'ah 'al)) (Reg 'rax)]
        [(ByteReg (or 'bh 'bl)) (Reg 'rbx)]
        [(ByteReg (or 'ch 'cl)) (Reg 'rcx)]
        [(ByteReg (or 'dh 'dl)) (Reg 'rdx)]
        [arg arg]))

    (define/public (pass-uncover-live p)
      (match p
        [(ProgramDefs info defs)
 
         (define/match (uncover-live-Def def)
           [((Def name '() 'Integer info blocks))
      
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
      
            (define cfg-t
              (let ([gr (make-multigraph '())])
                (for ([(curr-label block) (in-dict blocks)])
                  (add-vertex! gr curr-label)
                  (for ([instr (Block-instr* block)])
                    (match instr
                      [(or (Jmp label) (JmpIf _ label))
                       #:when (dict-has-key? blocks label)
                       (add-vertex! gr label)
                       (add-directed-edge! gr label curr-label)]
                      [_ '()])))
                gr))
      
            (analyse-dataflow cfg-t transfer (set) set-union*) 
            
            (Def name '() 'Integer info
              (hash-map/copy blocks
                (lambda (label block)
                  (values label
                    (Block
                      (dict-set (Block-info block)
                        'live-afters
                        (dict-ref label->live-afters label))
                      (Block-instr* block))))))])
   
         (ProgramDefs info (map uncover-live-Def defs))]))

    (define/public (pass-build-interference p)
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
               (for ([v live-set] #:when (and (Var? v) (dict-has-key? locals-types (Var-name v)) (gc-type? (dict-ref locals-types (Var-name v)))))
                 (for ([r (callee-saved-registers)])
                   (add-edge! gr v r))))))
      
         (for ([(label block) (in-dict blocks)])
           (update-graph (dict-ref (Block-info block) 'live-afters) (Block-instr* block)))
      
         (Def name '() 'Integer (dict-set info 'conflicts gr) blocks)])
         
      (define/match (build-move-graph-Def def)
        [((Def name '() 'Integer info blocks))
         (define gr (undirected-graph '()))
         (for ([location (append (map (lambda (p) (Var (car p))) (dict-ref info 'locals-types))
                                 (map Reg '(rax rbx rcx rdx rsi rdi rsp rbp r8 r9 r10 r11 r12 r13 r14 r15)))])
           (add-vertex! gr location))
         (for ([(label block) (in-dict blocks)])
           (for ([instr (Block-instr* block)])
             (match instr
               [(Instr 'movq (list a b))
                (add-edge! gr a b)]
               [_ '()])))
         (Def name '() 'Integer (dict-set info 'move-graph gr) blocks)])
                         
      (match p
        [(ProgramDefs info defs)
         (ProgramDefs info (map build-move-graph-Def (map build-interference-Def defs)))]))

    (define/public (pass-allocate-registers p)
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
            
         (define num-regs 11)
      
         (define variables (map (lambda (p) (Var (car p))) (dict-ref info 'locals-types)))
         (define interference (dict-ref info 'conflicts))
         (define location->color (make-hash (map (lambda (p) (cons (cdr p) (car p))) color->reg)))
         (struct Sat [location forbids prefers])
         (define queue
           (make-pqueue
             (lambda (a b)
               (let ([sat-a (set-count (Sat-forbids a))]
                     [sat-b (set-count (Sat-forbids b))])
                 (or (> sat-a sat-b)
                   (and (= sat-a sat-b)
                     (>= (set-count (Sat-prefers a)) (set-count (Sat-prefers b)))))))))
         (define variable->handle (make-hash))
      
         (define (get-saturation v)
           (for/set ([u (in-neighbors interference v)]
                     #:when (dict-has-key? location->color u))
             (dict-ref location->color u)))
                  
         (define (get-colored-move-related v)
           (for/set ([u (in-neighbors (dict-ref info 'move-graph) v)]
                     #:when (nonnegative-integer? (dict-ref location->color u -1)))
             (dict-ref location->color u)))
      
         (define (choose-color sat)
           (let* ([greedy (sequence-ref (sequence-filter (lambda (n) (not (set-member? (Sat-forbids sat) n))) (in-naturals 0)) 0)]
                  [preferred (set-subtract (Sat-prefers sat) (Sat-forbids sat))])
             (if (and (< greedy num-regs) (not (set-empty? preferred)) (>= (apply min (set->list preferred)) num-regs))
               greedy
               (apply min greedy (set->list preferred)))))
      
         (for ([v variables])
           (let ([hdl (pqueue-push! queue (Sat v (get-saturation v) (get-colored-move-related v)))])
             (dict-set! variable->handle v hdl)))
      
         (for ([i (in-range (pqueue-count queue))])
           (let* ([v (pqueue-pop! queue)]
                  [c (choose-color v)])
             (dict-set! location->color (Sat-location v) c)
             (for ([u (in-neighbors interference (Sat-location v))]
                   #:when (Var? u))
               (let ([hdl (dict-ref variable->handle u)])
                 (set-node-key! hdl (Sat u (get-saturation u) (get-colored-move-related u)))
                 (pqueue-decrease-key! queue hdl)))
             (for ([u (in-neighbors (dict-ref info 'move-graph) (Sat-location v))]
                   #:when (Var? u))
               (let ([hdl (dict-ref variable->handle u)])
                 (set-node-key! hdl (Sat u (get-saturation u) (get-colored-move-related u)))
                 (pqueue-decrease-key! queue hdl)))))
      
         (define locals-types (dict-ref info 'locals-types))
         (define-values (variable->reg variable->stack variable->root)
           (let-values ([(reg-variables stack-variables root-variables)
                         (for/fold ([reg-variables '()] [stack-variables '()] [root-variables '()])
                                   ([(location color) (in-dict location->color)])
                           (if (>= color num-regs)
                             (if (gc-type? (dict-ref locals-types (Var-name location)))
                               (values reg-variables stack-variables (cons (cons location color) root-variables))
                               (values reg-variables (cons (cons location color) stack-variables) root-variables))
                             (values (cons (cons location color) reg-variables) stack-variables root-variables)))])
             (values
               (make-immutable-hash (for/list ([p reg-variables] #:when (Var? (car p))) (cons (car p) (dict-ref color->reg (cdr p)))))
               (make-immutable-hash (for/list ([p stack-variables] [i (in-naturals)]) (cons (car p) (Deref 'rbp (* -8 (+ 1 i))))))
               (make-immutable-hash (for/list ([p root-variables] [i (in-naturals)]) (cons (car p) (Deref 'r15 (* -8 (+ 1 i)))))))))
            
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
           (set-intersect (list->set (callee-saved-registers)) (list->set (dict-values variable->reg))))
         (define stack-variables-size (* 8 (dict-count variable->stack)))
         (define new-info
           (list
             'num-root-spills (dict-count variable->root)
             'used-callee-saved-registers used-callee-saved-registers
             'stack-variables-size stack-variables-size))
      
         (Def name '() 'Integer (apply dict-set* info new-info)
           (hash-map/copy blocks
             (lambda (label block)
               (values label (Block (Block-info block) (map transform-instr (Block-instr* block)))))))])
   
      (match p
        [(ProgramDefs info defs)
         (ProgramDefs info (map allocate-registers-Def defs))]))
         
    (define/public (patch-instructions-instr instr)
      (match instr
        [(Instr 'leaq (list a b))
         #:when (not (Reg? b))
         (list
           (Instr 'leaq (list a (Reg 'rax)))
           (Instr 'leaq (list (Reg 'rax) b)))]
        [(TailJmp a arity)
         #:when (not (equal? a (Reg 'rax)))
         (list
           (Instr 'movq (list a (Reg 'rax)))
           (TailJmp (Reg 'rax) arity))]
        [(Instr (or 'movq 'movzbq) (list a b))
         #:when (equal? a b)
         '()]
        [(Instr op (list (Deref reg1 off1) (Deref reg2 off2)))
         (list
           (Instr 'movq (list (Deref reg1 off1) (Reg 'rax)))
           (Instr op (list (Reg 'rax) (Deref reg2 off2))))]
        [(Instr 'cmpq (list a (Imm b)))
         (list
           (Instr 'movq (list (Imm b) (Reg 'rax)))
           (Instr 'cmpq (list a (Reg 'rax))))]
        [(Instr 'movzbq (list a b))
         #:when (not (Reg? b))
         (list
           (Instr 'movzbq (list a (Reg 'rax)))
           (Instr 'movq (list (Reg 'rax) b)))]
        [_ (list instr)]))

    (define/public (pass-patch-instructions p)
      (define/match (patch-instructions-Def def)
        [((Def name '() 'Integer info blocks))
       
         (Def name '() 'Integer info
           (hash-map/copy blocks
             (lambda (label block)
               (values label
                 (Block (Block-info block)
                   (concat
                     (map (lambda (x) (patch-instructions-instr x))
                       (Block-instr* block))))))))])
      
      (match p
        [(ProgramDefs info defs)
         (ProgramDefs info (map patch-instructions-Def defs))]))

    (define/public (pass-prelude-and-conclusion p)
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
            `(,@finalize-root-stack
              ,@restore-registers
              ,@deallocate-stack-variables
              ,(Instr 'popq (list (Reg 'rbp)))
              ,(IndirectJmp f))]
           [(_) (list instr)])
      
         (set! blocks
           (for/hash ([(label block) (in-dict blocks)])
             (match block
               [(Block info instrs) (values label (Block info (concat (map transform-instr instrs))))])))
      
         (dict-set* blocks
           name
           (Block '()
             `(,(Instr 'pushq (list (Reg 'rbp)))
               ,(Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))
               ,@allocate-stack-variables
               ,@save-registers
               ,@(if (equal? name 'main) initialize-gc '())
               ,@initialize-root-stack
               ,(Jmp (symbol-append name 'start))))
                 
           (symbol-append name 'conclusion)
           (Block '()
             `(,@finalize-root-stack
               ,@restore-registers
               ,@deallocate-stack-variables
               ,(Instr 'popq (list (Reg 'rbp)))
               ,(Retq))))])
   
      (match p
        [(ProgramDefs info defs)
         (X86Program info (apply hash-union (map prelude-and-conclusion-Def defs)))]))
         
    (define/public (type-checker) type-check-Llambda)
    (define/public (interp) interp-Llambda)
    (define/public (test-specs)
      `(
        (0 "var")
        (0 "cond")
        (0 "while")
        (0 "vectors")
        (0 "functions")
        (0 "lambda")))
         
    (define/public (run-tests x86?)
      (AST-output-syntax 'concrete-syntax)
           
      (define all-tests
        (map (lambda (p) (car (string-split (path->string p) ".")))
             (filter (lambda (p)
                       (string=? (cadr (string-split (path->string p) ".")) "rkt"))
                     (directory-list (build-path (current-directory) "tests")))))

      (define (tests-for r)
        (map (lambda (p)
               (caddr (string-split p "_")))
             (filter
              (lambda (p)
                (string=? r (car (string-split p "_"))))
              all-tests)))
      
      (for ([test (test-specs)])
        (match test
          [(list dl name)
           (debug-level dl)
           (interp-tests name (type-checker) (compiler-passes) (interp) (string-append name "_test") (tests-for name))]))
      (when x86?
        (for ([test (test-specs)])
          (match test
            [(list dl name)
             (debug-level dl)
             (compiler-tests name (type-checker) (compiler-passes) (string-append name "_test") (tests-for name))]))))
  
    (define/public (compiler-passes)
      (define (annotate-var-type e)
        (parameterize ([typed-vars #t])
          (type-check-Llambda e)))
      `(("shrink"                   ,(lambda (x) (pass-shrink x)) ,interp-Llambda ,type-check-Llambda)
        ("uniquify"                 ,(lambda (x) (pass-uniquify x)) ,interp-Llambda ,type-check-Llambda)
        ("reveal FunRef"            ,(lambda (x) (pass-reveal-functions x)) ,interp-Llambda-prime ,type-check-Llambda)
        ("convert assignments"      ,(lambda (x) (pass-convert-assignments x)) ,interp-Llambda-prime ,type-check-Llambda)
        ("annotate var types"       ,(lambda (x) x) ,interp-Llambda-prime ,annotate-var-type)
        ("convert closures"         ,(lambda (x) (pass-convert-closures x)) ,interp-Llambda-prime ,type-check-Llambda)
        ("limit funtion parameters" ,(lambda (x) (pass-limit-functions x)) ,interp-Llambda-prime ,type-check-Llambda)
        ("expose allocation"        ,(lambda (x) (pass-expose-allocation x)) ,interp-Llambda-prime ,type-check-Llambda)
        ("uncover get!"             ,(lambda (x) (pass-uncover-get! x)) ,interp-Llambda-prime ,type-check-Llambda)
        ("remove complex operands"  ,(lambda (x) (pass-remove-complex-operands x)) ,interp-Llambda-prime ,type-check-Llambda)
        ("explicate control"        ,(lambda (x) (pass-explicate-control x)) ,interp-Clambda ,type-check-Clambda)
        ("optimize blocks"          ,(lambda (x) (pass-optimize-blocks x)) ,interp-Clambda ,type-check-Clambda)
        ("instruction selection"    ,(lambda (x) (pass-select-instructions x)) ,interp-SSA)
        ("build dominance"          ,(lambda (x) (pass-build-dominance x)) ,interp-SSA)))))
        ;("liveness analysis"        ,(lambda (x) (pass-uncover-live x)) ,interp-x86-4)
        ;("build interference graph" ,(lambda (x) (pass-build-interference x)) ,interp-x86-4)
        ;("allocate registers"       ,(lambda (x) (pass-allocate-registers x)) ,interp-x86-4)
        ;("patch instructions"       ,(lambda (x) (pass-patch-instructions x)) ,interp-x86-4)
        ;("prelude and conclusion"   ,(lambda (x) (pass-prelude-and-conclusion x)) #f)))))

(module* main #f
  (send (new compiler-Llambda) run-tests #f))

#! /usr/bin/env -S nix shell nixpkgs#racket --command racket
#lang racket
(require "interp-Ldyn.rkt")
(require "interp-Lany.rkt")
(require "interp-Lany-prime.rkt")
(require "type-check-Lany.rkt")
(require "type-check-Llambda.rkt")
(require "interp-Cany.rkt")
(require "type-check-Cany.rkt")
(require "utilities.rkt")
(require "interp.rkt")
(require "compiler-Llambda.rkt")
(provide (all-defined-out))

(define compiler-Ldyn
  (class compiler-Llambda
    (inherit
      append-point convert-closure-type remove-complex-operands-atom
      let-bindings select-instructions-atom argument-passing-registers location?
      set-filter
      pass-shrink pass-reveal-functions pass-convert-assignments pass-limit-functions
      pass-expose-allocation pass-uncover-get! pass-remove-complex-operands
      pass-explicate-control pass-optimize-blocks pass-select-instructions pass-uncover-live
      pass-build-interference pass-patch-instructions pass-allocate-registers
      pass-prelude-and-conclusion
      pass-build-dominance pass-convert-from-SSA pass-convert-to-SSA)
    (super-new)
    
    (define/public (type-tag ty)
      (match ty
        ['Integer #b001]
        ['Boolean #b100]
        [`(Vector ,_ ...) #b010]
        [`(,_ ... -> ,_) #b011]
        ['Void #b101]))

    (define/override (gc-type? ty)
      (if (equal? ty 'Any)
        #t
        (super gc-type? ty)))
         
    (define/override ((induct-L f) exp)
      (match exp
        [(Inject e t) (f (Inject ((induct-L f) e) t))]
        [(Project e t) (f (Project ((induct-L f) e) t))]
        [(ValueOf e t) (f (ValueOf ((induct-L f) e) t))]
        [(Exit) (f exp)]
        [exp ((super induct-L f) exp)]))
         
    (define/override (subexpressions exp)
      (match exp
        [(or (Inject e _) (Project e _) (ValueOf e _)) (list e)]
        [(Exit) '()]
        [exp (super subexpressions exp)]))

    (define/public (strip-types prog)

      (define/match (strip-types-param param)
        [((list x ': _)) x]
        [(x) x])
  
      (define strip-types-exp
        (induct-L
          (match-lambda
            [(Lambda params rty body) (Lambda (map strip-types-param params) '_ body)]
            [exp exp])))
   
      (define/match (strip-types-Def def)
        [((Def name params rty info body))
         (Def name (map strip-types-param params) '_ info (strip-types-exp body))])
      
      (match prog
        [(ProgramDefsExp info defs exp)
         (ProgramDefsExp info (map strip-types-Def defs) (strip-types-exp exp))]
        [(Program info exp)
         (Program info (strip-types-exp exp))]))
   
    (define (param-name p)
      (match p
        [`(,x : ,t) x]
        [x #:when (symbol? x) x]))
         
    (define/override (uniquify-exp env)
      (match-lambda
        [(Lambda params rty body)
         (define new-env
           (for/fold ([new-env env]) ([p params])
             (dict-set new-env (param-name p) (gensym (append-point (param-name p))))))
         (Lambda
           (for/list ([p params])
             (match p
               [`(,x : ,t) `(,(dict-ref new-env x) : ,t)]
               [x (dict-ref new-env x)]))
           rty
           ((uniquify-exp new-env) body))]
        [exp ((super uniquify-exp env) exp)]))
         
    (define/override (pass-uniquify p)
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
                    (dict-set new-env (param-name p) (gensym (append-point (param-name p))))))
                (Def
                  name
                  (for/list ([p params])
                    (match p
                      [`(,x : ,t) `(,(dict-ref new-env x) : ,t)]
                      [x (dict-ref new-env x)]))
                  rty
                  info
                  ((uniquify-exp new-env) body))])))]))

    (define/public (pass-insert-casts p)
      (define insert-casts-exp
        (induct-L
          (match-lambda
            [(Int i) (Inject (Int i) 'Integer)]
            [(Bool b) (Inject (Bool b) 'Boolean)]
            [(FunRef f n) (Inject (FunRef f n) `(,@(for/list ([_ (in-range n)]) 'Any) -> Any))]
            [(and exp (or (SetBang _ _) (Void)))
             (Inject exp 'Void)]
            [(Lambda `(,ps ...) _ body)
             (Inject (Lambda (for/list ([p ps]) `(,p : Any)) 'Any body)
                     `(,@(for/list ([_ ps]) 'Any) -> Any))]
            [(Prim 'read '()) (Inject (Prim 'read '()) 'Integer)]
            [(Prim (and op (or '+ '-)) args)
             (Inject (Prim op (for/list ([a args]) (Project a 'Integer))) 'Integer)]
            [(Prim (and op (or '< '<= '> '>=)) args)
             (Inject (Prim op (for/list ([a args]) (Project a 'Integer))) 'Boolean)]
            [(Prim 'eq? args)
             (Inject (Prim 'eq? args) 'Boolean)]
            [(Prim (and op (or 'and 'or)) args)
             (Inject (Prim op (for/list ([a args]) (Project a 'Boolean))) 'Boolean)]
            [(Prim 'vector-ref (list v i))
             (Prim 'any-vector-ref (list v (Project i 'Integer)))]
            [(Prim 'vector-set! (list v i e))
             (Prim 'any-vector-set! (list v (Project i 'Integer) e))]
            [(Prim 'vector args)
             (Inject (Prim 'vector args) `(Vector ,@(for/list ([_ args]) 'Any)))]
            [(Prim 'vector-length args)
             (Inject (Prim 'any-vector-length args) 'Integer)]
            [(Prim 'procedure-arity (list f))
             (define f-var (gensym 'procedure-arity.f.))
             (Let f-var f
               (If (Prim 'eq? (list (Prim 'tag-of-any (list (Var f-var)))
                                    (Int (type-tag '(-> Integer)))))
                 (Inject (Prim 'procedure-arity (list (ValueOf (Var f-var) '(-> Integer))))
                         'Integer)
                 (Exit)))]
            [(Apply f args)
             (Apply (Project f `(,@(for/list ([_ args]) 'Any) -> Any)) args)]
            [(If c t e)
             (If (Prim 'eq? (list c (Inject (Bool #f) 'Boolean)))
                 e
                 t)]
            [(Prim 'not (list a))
             (If (Prim 'eq? (list a (Inject (Bool #f) 'Boolean)))
               (Inject (Bool #t) 'Boolean)
               (Inject (Bool #f) 'Boolean))]
            [(WhileLoop c e)
             (Inject
               (WhileLoop
                 (Prim 'not (list (Prim 'eq? (list c (Inject (Bool #f) 'Boolean)))))
                 e)
               'Void)]
            [(Prim (and op (or 'boolean? 'integer? 'vector? 'procedure? 'void?)) args)
             (Inject (Prim op args) 'Boolean)]
            [exp exp])))
   
      (define/match (insert-casts-Def def)
        [((Def name params _ info body))
         (Def
           name
           (for/list ([p params]) `(,p : Any))
           (if (equal? name 'main) 'Integer 'Any)
           info
           (if (equal? name 'main)
             (Project (insert-casts-exp body) 'Integer)
             (insert-casts-exp body)))])
   
      (match p
        [(ProgramDefs info defs)
         (ProgramDefs info (map insert-casts-Def defs))]))
  
    (define/public (pass-reveal-casts p)
      (define type-pred->type-tag
        (hash
          'boolean? (type-tag 'Boolean)
          'integer? (type-tag 'Integer)
          'vector? (type-tag '(Vector))
          'procedure? (type-tag '(-> _))
          'void? (type-tag 'Void)))
   
      (define reveal-casts-exp
        (induct-L
          (match-lambda
            [(Project e ty)
             (define tmp-var (gensym 'project.))
             (Let tmp-var e
               (If (Prim 'eq? (list (Prim 'tag-of-any (list (Var tmp-var)))
                                    (Int (type-tag ty))))
                 (match ty
                   [`(Vector ,ts ...)
                    (define vec-var (gensym 'vector.))
                    (Let vec-var (ValueOf (Var tmp-var) ty)
                      (If (Prim 'eq? (list (Prim 'vector-length (list (Var vec-var))) (Int (length ts))))
                        (Var vec-var)
                        (Exit)))]
                   [`(,ts ... -> ,_)
                    (define clos-var (gensym 'closure.))
                    (Let clos-var (ValueOf (Var tmp-var) ty)
                      (If (Prim 'eq? (list (Prim 'procedure-arity (list (Var clos-var))) (Int (length ts))))
                        (Var clos-var)
                        (Exit)))]
                   [_ (ValueOf (Var tmp-var) ty)])
                 (Exit)))]
            [(Inject e ty)
             (Prim 'make-any (list e (Int (type-tag ty))))]
            [(Prim op (list e))
             #:when (dict-has-key? type-pred->type-tag op)
             (Prim 'eq? (list (Prim 'tag-of-any (list e)) (Int (dict-ref type-pred->type-tag op))))]
            [(Prim 'any-vector-ref (list v i))
             (define v-var (gensym 'any-vector-ref.vector.))
             (define i-var (gensym 'any-vector-ref.index.))
             (Let v-var v
               (Let i-var i
                 (If (Prim 'eq? (list (Prim 'tag-of-any (list (Var v-var)))
                                      (Int (type-tag '(Vector)))))
                   (If (Prim '< (list (Var i-var)
                                      (Prim 'any-vector-length (list (Var v-var)))))
                     (Prim 'any-vector-ref (list (Var v-var) (Var i-var)))
                     (Exit))
                   (Exit))))]
            [(Prim 'any-vector-length (list v))
             (define v-var (gensym 'any-vector-length.vector.))
             (Let v-var v
               (If (Prim 'eq? (list (Prim 'tag-of-any (list (Var v-var)))
                                    (Int (type-tag '(Vector)))))
                 (Prim 'any-vector-length (list (Var v-var)))
                 (Exit)))]
            [(Prim 'any-vector-set! (list v i e))
             (define v-var (gensym 'any-vector-set!.vector.))
             (define i-var (gensym 'any-vector-set!.index.))
             (Let v-var v
               (Let i-var i
                 (If (Prim 'eq? (list (Prim 'tag-of-any (list (Var v-var)))
                                      (Int (type-tag '(Vector)))))
                   (If (Prim '< (list (Var i-var)
                                      (Prim 'any-vector-length (list (Var v-var)))))
                     (Prim 'any-vector-set! (list (Var v-var) (Var i-var) e))
                     (Exit))
                   (Exit))))]
            [exp exp])))
   
      (define/match (reveal-casts-Def def)
        [((Def name params rty info body))
         (Def name params rty info (reveal-casts-exp body))])
   
      (match p
        [(ProgramDefs info defs)
         (ProgramDefs info (map reveal-casts-Def defs))]))

    (define/override (pass-convert-closures p)
      (match (super pass-convert-closures p)
        [(ProgramDefs info defs)
   
         (define convert-exp
           (induct-L
             (match-lambda
               [(ValueOf e t)
                (ValueOf e (convert-closure-type t))]
               [exp exp])))
   
         (define/match (convert-Def def)
           [((Def name params rty info body))
            (Def name params rty info (convert-exp body))])
   
         (ProgramDefs info (map convert-Def defs))]))

    (define/override (remove-complex-operands-exp-induct exp)
      (match exp
        [(ValueOf e t)
         (define-values (bindings atom) (remove-complex-operands-atom e))
         (let-bindings bindings (ValueOf atom t))]
        [e (super remove-complex-operands-exp-induct e)]))

    (define/override (complex-exp? exp)
      (match exp
        [(ValueOf _ _) (gensym 'value-of.)]
        [(Exit) (gensym 'exit.)]
        [exp (super complex-exp? exp)]))

    (define/override (explicate-effects effs cont)
      (match effs
        [(cons (Exit) effs)
         (Exit)]
        [(cons (Prim 'any-vector-set! args) effs)
         (explicate-assign (gensym 'not.used.) (Prim 'any-vector-set! args) (explicate-effects effs cont))]
        [effs (super explicate-effects effs cont)]))

    (define/override (explicate-if c t e)
      (match c
        [(Exit) (Exit)]
        [c (super explicate-if c t e)]))

    (define/override (explicate-assign x e cont)
      (match e
        [(Exit) (Exit)]
        [e (super explicate-assign x e cont)]))

    (define/override (explicate-tail e)
      (match e
        [(Exit) (Exit)]
        [e (super explicate-tail e)]))
         
    (define/override (convert-to-SSA-rename-C! get-latest-name gen-fresh-name! prog)
      (define (recur! p) (convert-to-SSA-rename-C! get-latest-name gen-fresh-name! p))
      (match prog
        [(ValueOf x ty) (ValueOf (recur! x) ty)]
        [(Exit) (Exit)]
        [_ (super convert-to-SSA-rename-C! get-latest-name gen-fresh-name! prog)]))

    (define/override (select-instructions-stmt s)
      (match s
        [(Assign x (Prim 'make-any (list e (Int tag))))
         #:when (= 2 (bitwise-and tag 2))
         (list
           (Instr 'movq (list (select-instructions-atom e) x))
           (Instr 'orq (list (Imm tag) x)))]
        [(Assign x (Prim 'make-any (list e (Int tag))))
         #:when (= 0 (bitwise-and tag 2))
         (list
           (Instr 'movq (list (select-instructions-atom e) x))
           (Instr 'salq (list (Imm 3) x))
           (Instr 'orq (list (Imm tag) x)))]
        [(Assign x (Prim 'tag-of-any (list e)))
         (list
           (Instr 'movq (list (select-instructions-atom e) x))
           (Instr 'andq (list (Imm 7) x)))]
        [(Assign x (ValueOf e t))
         #:when (pair? t)
         (list
           (Instr 'movq (list (Imm -8) x))
           (Instr 'andq (list (select-instructions-atom e) x)))]
        [(Assign x (ValueOf e t))
         #:when (symbol? t)
         (list
           (Instr 'movq (list (select-instructions-atom e) x))
           (Instr 'sarq (list (Imm 3) x)))]
        [(Assign x (Prim 'any-vector-length (list v)))
         (list
           (Instr 'movq (list (Imm -8) (Reg 'r11)))
           (Instr 'andq (list (select-instructions-atom v) (Reg 'r11)))
           (Instr 'movq (list (Deref 'r11 0) (Reg 'r11)))
           (Instr 'sarq (list (Imm 1) (Reg 'r11)))
           (Instr 'andq (list (Imm 63) (Reg 'r11)))
           (Instr 'movq (list (Reg 'r11) x)))]
        [(Assign x (Prim 'any-vector-ref (list v i)))
         (list
           (Instr 'movq (list (Imm -8) (Reg 'r11)))
           (Instr 'andq (list (select-instructions-atom v) (Reg 'r11)))
           (Instr 'movq (list (select-instructions-atom i) (Reg 'rax)))
           (Instr 'addq (list (Imm 1) (Reg 'rax)))
           (Instr 'imulq (list (Imm 8) (Reg 'rax)))
           (Instr 'addq (list (Reg 'rax) (Reg 'r11)))
           (Instr 'movq (list (Deref 'r11 0) x)))]
        [(Assign x (Prim 'any-vector-set! (list v i e)))
         (list
           (Instr 'movq (list (Imm -8) (Reg 'r11)))
           (Instr 'andq (list (select-instructions-atom v) (Reg 'r11)))
           (Instr 'movq (list (select-instructions-atom i) (Reg 'rax)))
           (Instr 'addq (list (Imm 1) (Reg 'rax)))
           (Instr 'imulq (list (Imm 8) (Reg 'rax)))
           (Instr 'addq (list (Reg 'rax) (Reg 'r11)))
           (Instr 'movq (list (select-instructions-atom e) (Reg 'r11)))
           (Instr 'movq (list (Imm (type-tag 'Void)) x)))]
        [s (super select-instructions-stmt s)]))

    (define/override (select-instructions-tail name tail)
      (match tail
        [(Exit)
         (list
           (Instr 'movq (list (Imm 255) (car (argument-passing-registers))))
           (Callq 'exit 1))]
        [tail (super select-instructions-tail name tail)]))

    (define/override (locations-written instr)
      (match instr
        [(Instr (or 'imulq 'orq 'salq) (list _ b))
         (if (location? b)
           (set b)
           (set))]
        [instr (super locations-written instr)]))

    (define/override (locations-read instr)
      (match instr
        [(Instr (or 'imulq 'orq 'salq) args)
         (set-filter (lambda (x) (location? x))
           (list->set args))]
        [instr (super locations-read instr)]))
         
    (define/override (interp) interp-Ldyn)
    (define/override (type-checker) (lambda (x) (strip-types x)))
    (define/override (test-specs)
      `(
        (0 "var")
        (0 "cond")
        (0 "while")
        (0 "vectors")
        (0 "functions")
        (0 "lambda")
        (0 "dynamic")))
  
    (define/override (compiler-passes)
      (define (annotate-var-type e)
        (parameterize ([typed-vars #t])
          (type-check-Lany e)))
      `(("shrink"                   ,(lambda (x) (pass-shrink x)) ,interp-Ldyn-prog)
        ("uniquify"                 ,(lambda (x) (pass-uniquify x)) ,interp-Ldyn-prog)
        ("reveal FunRef"            ,(lambda (x) (pass-reveal-functions x)) ,interp-Ldyn-prog)
        ("insert casts"             ,(lambda (x) (pass-insert-casts x)) ,interp-Lany-prime ,type-check-Lany)
        ("reveal casts"             ,(lambda (x) (pass-reveal-casts x)) ,interp-Lany-prime ,type-check-Lany)
        ("convert assignments"      ,(lambda (x) (pass-convert-assignments x)) ,interp-Lany-prime ,type-check-Lany)
        ("annotate var types"       ,(lambda (x) x) ,interp-Lany-prime ,annotate-var-type)
        ("convert closures"         ,(lambda (x) (pass-convert-closures x)) ,interp-Lany-prime ,type-check-Lany)
        ("limit funtion parameters" ,(lambda (x) (pass-limit-functions x)) ,interp-Lany-prime ,type-check-Lany)
        ("expose allocation"        ,(lambda (x) (pass-expose-allocation x)) ,interp-Lany-prime ,type-check-Lany)
        ("uncover get!"             ,(lambda (x) (pass-uncover-get! x)) ,interp-Lany-prime ,type-check-Lany)
        ("remove complex operands"  ,(lambda (x) (pass-remove-complex-operands x)) ,interp-Lany-prime ,type-check-Lany)
        ("explicate control"        ,(lambda (x) (pass-explicate-control x)) ,interp-Cany ,type-check-Cany)
        ("optimize blocks"          ,(lambda (x) (pass-optimize-blocks x)) ,interp-Cany ,type-check-Cany)
        ("build dominance"          ,(lambda (x) (pass-build-dominance x)) ,interp-Cany ,type-check-Cany)
        ("convert to SSA"           ,(lambda (x) (pass-convert-to-SSA x)) ,interp-Cany ,type-check-Cany)
        ("convert from SSA"         ,(lambda (x) (pass-convert-from-SSA x)) ,interp-Cany ,type-check-Cany)
        ("instruction selection"    ,(lambda (x) (pass-select-instructions x)) ,interp-x86-4)
        ("liveness analysis"        ,(lambda (x) (pass-uncover-live x)) ,interp-x86-4)
        ("build interference graph" ,(lambda (x) (pass-build-interference x)) ,interp-x86-4)
        ("allocate registers"       ,(lambda (x) (pass-allocate-registers x)) ,interp-x86-4)
        ("patch instructions"       ,(lambda (x) (pass-patch-instructions x)) ,interp-x86-4)
        ("prelude and conclusion"   ,(lambda (x) (pass-prelude-and-conclusion x)) #f)))))
    
(module* main #f
  (send (new compiler-Ldyn) run-tests #t))

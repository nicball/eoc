#! /usr/bin/env -S nix shell nixpkgs#racket --command racket
#lang racket
(require "compiler-Ldyn.rkt")
(require "interp-Lcast.rkt")
(require "interp-Lcast-prime.rkt")
(require "type-check-gradual.rkt")
(require "type-check-Llambda.rkt")
(require "interp-Cany-proxy.rkt")
(require "utilities.rkt")
(require "interp.rkt")
(provide (all-defined-out))

(define compiler-gradual
  (class compiler-Ldyn
    (inherit
      pass-shrink pass-uniquify pass-reveal-functions pass-reveal-casts
      pass-convert-assignments pass-convert-closures pass-limit-functions
      pass-expose-allocation pass-uncover-get! pass-remove-complex-operands
      pass-explicate-control pass-optimize-blocks pass-select-instructions pass-uncover-live
      pass-build-interference pass-allocate-registers pass-patch-instructions
      pass-prelude-and-conclusion
      explicate-assign select-instructions-atom)
    (super-new)
         
    (define/override (type-tag ty)
      (match ty
        [`(PVector ,_ ...) #b010]
        [ty (super type-tag ty)]))
         
    (define/override ((induct-L f) exp)
      (match exp
        [(Cast e s t) (f (Cast ((induct-L f) e) s t))]
        [exp ((super induct-L f) exp)]))

    (define/public (pass-lower-casts p)
      (define (apply-cast exp source target)
        (match* (source target)
          [(_ _) #:when (equal? source target) exp]
         
          [('Any `(,arg-tys ... -> ,rty))
           (define any->any `(,@(for/list ([_ arg-tys]) 'Any) -> Any))
           (apply-cast
             (Project exp any->any)
             any->any
             target)]
          [('Any `(Vector ,elem-tys))
           (define vector-any `(Vector ,@(for/list ([_ elem-tys]) 'Any)))
           (apply-cast
             (Project exp vector-any)
             vector-any
             target)]
          [('Any _)
           (Project exp target)]
         
          [(`(,arg-tys ... -> ,rty) 'Any)
           (define any->any `(,@(for/list ([_ arg-tys]) 'Any) -> Any))
           (Inject
             (apply-cast exp source any->any)
             'Any)]
          [(`(Vector ,elem-tys) 'Any)
           (define vector-any `(Vector ,@(for/list ([_ elem-tys]) 'Any)))
           (Inject
             (apply-cast exp vector-any target)
             'Any)]
          [(_ 'Any)
           (Inject exp source)]
         
          [(`(Vector ,se-tys ...) `(Vector ,te-tys ...))
           (define readers
             (for/list ([src se-tys] [tgt te-tys])
               (define arg (gensym 'reader-arg.))
               (Lambda `((,arg : ,src)) tgt
                 (apply-cast (Var arg) src tgt))))
           (define writers
             (for/list ([src se-tys] [tgt te-tys])
               (define arg (gensym 'writer-arg.))
               (Lambda `((,arg : ,tgt)) src
                 (apply-cast (Var arg) tgt src))))
           (Prim 'vector-proxy
             (list exp (Prim 'raw-vector readers) (Prim 'raw-vector writers)))]

          [(`(,sa-tys ... -> ,srty) `(,ta-tys ... -> ,trty))
           (define args (for/list ([_ ta-tys]) (gensym 'lambda-proxy-arg.)))
           (Lambda
             (for/list ([x args] [t ta-tys])
               `(,x : ,t))
             trty
             (apply-cast
               (Apply exp
                 (for/list ([x args] [s ta-tys] [t sa-tys])
                   (apply-cast (Var x) s t)))
               srty
               trty))]))
   
      (define lower-casts-exp
        (induct-L
          (match-lambda
            [(Cast e s t) (apply-cast e s t)]
            [exp exp])))
   
      (define/match (lower-casts-Def def)     
        [((Def name params rty info body))
         (Def name params rty info (lower-casts-exp body))])

      (match p
        [(Program info exp)
         (Program info (lower-casts-exp exp))]
             
        [(ProgramDefsExp info defs exp)
         (ProgramDefsExp info (map lower-casts-Def defs) (lower-casts-exp exp))]))

    (define/public (pass-differentiate-proxies p)
      (define/match (differentiate-proxies-type ty)
        [(`(Vector ,tys ...)) `(PVector ,@(map differentiate-proxies-type tys))]
        [(`(,arg-tys ... -> ,rty)) `(,@(map differentiate-proxies-type arg-tys) -> ,(differentiate-proxies-type rty))]
        [(ty) ty])
 
      (define differentiate-proxies-exp
        (induct-L
          (match-lambda
            [(HasType (Prim 'vector args) _)
             (Prim 'inject-vector (list (Prim 'vector args)))]
            [(Project e t) (Project e (differentiate-proxies-type t))]
            [(Inject e t) (Inject e (differentiate-proxies-type t))]
            [(Prim 'raw-vector args)
             (Prim 'vector args)]
            [(Prim 'vector-proxy args)
             (Prim 'inject-proxy (list (Prim 'vector args)))]
            [(Prim 'vector-ref (list v i))
             (define pv (gensym 'pvector.))
             (Let pv v
               (If (Prim 'proxy? (list (Var pv)))
                 (Prim 'proxy-vector-ref (list (Var pv) i))
                 (Prim 'vector-ref (list (Prim 'project-vector (list (Var pv))) i))))]
            [(Prim 'vector-set! (list v i e))
             (define pv (gensym 'pvector.))
             (Let pv v
               (If (Prim 'proxy? (list (Var pv)))
                 (Prim 'proxy-vector-set! (list (Var pv) i e))
                 (Prim 'vector-set! (list (Prim 'project-vector (list (Var pv))) i e))))]
            [(Prim 'vector-length (list v))
             (define pv (gensym 'pvector.))
             (Let pv v
               (If (Prim 'proxy? (list (Var pv)))
                 (Prim 'proxy-vector-length (list (Var pv)))
                 (Prim 'vector-length (list (Prim 'project-vector (list (Var pv)))))))]
            [(Lambda params rty body)
             (Lambda
               (for/list ([p params])
                 (match p
                   [`(,x : ,t) `(,x : ,(differentiate-proxies-type t))]))
               (differentiate-proxies-type rty)
               body)]
            [exp exp])))
   
      (define/match (differentiate-proxies-Def def)     
        [((Def name params rty info body))
         (Def
           name
           (for/list ([p params])
             (match p
               [`(,x : ,t) `(,x : ,(differentiate-proxies-type t))]))
           (differentiate-proxies-type rty)
           info
           (differentiate-proxies-exp body))])
   
      (match p
        [(Program info exp) 
         (Program info (differentiate-proxies-exp exp))]
             
        [(ProgramDefsExp info defs exp)
         (ProgramDefsExp info (map differentiate-proxies-Def defs) (differentiate-proxies-exp exp))]))
         
    (define/override (uniquify-exp env)
      (match-lambda
        [(Project e t) (Project ((uniquify-exp env) e) t)]
        [(Inject e t) (Inject ((uniquify-exp env) e) t)]
        [exp ((super uniquify-exp env) exp)]))

    (define/override (explicate-effects effs cont)
      (match effs
        [(cons (Prim 'proxy-vector-set! args) effs)
         (Seq (Prim 'proxy-vector-set! args) (explicate-effects effs cont))]
        [effs (super explicate-effects effs cont)]))

    (define/override (explicate-if c t e)
      (match c
        [(Prim op _)
         #:when (not (set-member? '(eq? < <= > >= not) op))
         (define cond-var (gensym 'if.cond.))
         (explicate-assign cond-var c (explicate-if (Var cond-var) t e))]
        [c (super explicate-if c t e)]))

    (define/override (select-instructions-stmt s)
      (match s
        [(Assign x (Prim 'inject-vector (list e)))
         (list (Instr 'movq (list (select-instructions-atom e) x)))]
        [(Assign x (Prim 'inject-proxy (list e)))
         (list
           (Instr 'movq (list (select-instructions-atom e) (Reg 'r11)))
           (Instr 'movq (list (Imm (arithmetic-shift 1 63)) (Reg 'rax)))
           (Instr 'orq (list (Reg 'rax) (Deref 'r11 0)))
           (Instr 'movq (list (Reg 'r11) x)))]
        [(Assign x (Prim 'proxy? (list e)))
         (list
           (Instr 'movq (list (select-instructions-atom e) (Reg 'r11)))
           (Instr 'movq (list (Deref 'r11 0) (Reg 'rax)))
           (Instr 'sarq (list (Imm 63) (Reg 'rax)))
           (Instr 'andq (list (Imm 1) (Reg 'rax)))
           (Instr 'movq (list (Reg 'rax) x)))]
        [(Assign x (Prim 'project-vector (list e)))
         (list (Instr 'movq (list (select-instructions-atom e) x)))]
        [(Assign x (Prim 'proxy-vector-set! (list v i e)))
         (list
           (Instr 'movq (list (select-instructions-atom v) (Reg 'rdi)))
           (Instr 'movq (list (select-instructions-atom i) (Reg 'rsi)))
           (Instr 'movq (list (select-instructions-atom e) (Reg 'rdx)))
           (Callq 'proxy_vector_set 3)
           (Instr 'movq (list (Reg 'rax) x)))]
        [(Prim 'proxy-vector-set! (list v i e))
         (list
           (Instr 'movq (list (select-instructions-atom v) (Reg 'rdi)))
           (Instr 'movq (list (select-instructions-atom i) (Reg 'rsi)))
           (Instr 'movq (list (select-instructions-atom e) (Reg 'rdx)))
           (Callq 'proxy_vector_set 3))]
        [(Assign x (Prim 'proxy-vector-ref (list v i)))
         (list
           (Instr 'movq (list (select-instructions-atom v) (Reg 'rdi)))
           (Instr 'movq (list (select-instructions-atom i) (Reg 'rsi)))
           (Callq 'proxy_vector_ref 2)
           (Instr 'movq (list (Reg 'rax) x)))]
        [(Assign x (Prim 'proxy-vector-length (list v)))
         (list
           (Instr 'movq (list (select-instructions-atom v) (Reg 'rdi)))
           (Callq 'proxy_vector_length 1)
           (Instr 'movq (list (Reg 'rax) x)))]
        [(Assign x (Prim 'any-vector-length (list v)))
         (list
           (Instr 'movq (list (Imm -8) (Reg 'rdi)))
           (Instr 'andq (list (select-instructions-atom v) (Reg 'rdi)))
           (Instr 'movq (list (Deref 'rdi 0) (Reg 'rdi)))
           (Callq 'proxy_vector_length 1)
           (Instr 'movq (list (Reg 'rax) x)))]
        [(Assign x (Prim 'any-vector-ref (list v i)))
         (list
           (Instr 'movq (list (Imm -8) (Reg 'rdi)))
           (Instr 'andq (list (select-instructions-atom v) (Reg 'rdi)))
           (Instr 'movq (list (Deref 'rdi 0) (Reg 'rdi)))
           (Instr 'movq (list (select-instructions-atom i) (Reg 'rsi)))
           (Callq 'proxy_vector_ref 2)
           (Instr 'movq (list (Reg 'rax) x)))]
        [(Assign x (Prim 'any-vector-set! (list v i e)))
         (list
           (Instr 'movq (list (Imm -8) (Reg 'rdi)))
           (Instr 'andq (list (select-instructions-atom v) (Reg 'rdi)))
           (Instr 'movq (list (Deref 'rdi 0) (Reg 'rdi)))
           (Instr 'movq (list (select-instructions-atom i) (Reg 'rsi)))
           (Instr 'movq (list (select-instructions-atom e) (Reg 'rdx)))
           (Callq 'proxy_vector_set 2)
           (Instr 'movq (list (Reg 'rax) x)))]
        [s (super select-instructions-stmt s)]))
         
    (define/override (interp) interp-Lcast)
    (define/override (type-checker) type-check-gradual)
    (define/override (test-specs)
      `(
        (0 "var")
        (0 "cond")
        (0 "while")
        (0 "vectors")
        (0 "functions")
        (0 "lambda")
        (0 "gradual")))
             
    (define/override (compiler-passes)
      (define (annotate-var-type e)
        (parameterize ([typed-vars #t])
          (type-check-Lany-proxy e)))
      `(
        ("lower casts"              ,(lambda (x) (pass-lower-casts x)) ,interp-Lcast ,type-check-Lany-proxy)
        ("differentiate proxies"    ,(lambda (x) (pass-differentiate-proxies x)) ,interp-Lcast ,type-check-Lany-proxy)
        ("shrink"                   ,(lambda (x) (pass-shrink x)) ,interp-Lcast ,type-check-Lany-proxy)
        ("uniquify"                 ,(lambda (x) (pass-uniquify x)) ,interp-Lcast ,type-check-Lany-proxy)
        ("reveal FunRef"            ,(lambda (x) (pass-reveal-functions x)) ,interp-Lcast-prime ,type-check-Lany-proxy)
        ("reveal casts"             ,(lambda (x) (pass-reveal-casts x)) ,interp-Lcast-prime ,type-check-Lany-proxy)
        ("convert assignments"      ,(lambda (x) (pass-convert-assignments x)) ,interp-Lcast-prime ,type-check-Lany-proxy)
        ("annotate var types"       ,(lambda (x) x) ,interp-Lcast-prime ,annotate-var-type)
        ("convert closures"         ,(lambda (x) (pass-convert-closures x)) ,interp-Lcast-prime ,type-check-Lany-proxy)
        ("limit funtion parameters" ,(lambda (x) (pass-limit-functions x)) ,interp-Lcast-prime ,type-check-Lany-proxy)
        ("expose allocation"        ,(lambda (x) (pass-expose-allocation x)) ,interp-Lcast-prime ,type-check-Lany-proxy)
        ("uncover get!"             ,(lambda (x) (pass-uncover-get! x)) ,interp-Lcast-prime ,type-check-Lany-proxy)
        ("remove complex operands"  ,(lambda (x) (pass-remove-complex-operands x)) ,interp-Lcast-prime ,type-check-Lany-proxy)
        ("explicate control"        ,(lambda (x) (pass-explicate-control x)) ,interp-Cany-proxy ,type-check-Cany-proxy)
        ("optimize blocks"          ,(lambda (x) (pass-optimize-blocks x)) ,interp-Cany-proxy ,type-check-Cany-proxy)
        ("instruction selection"    ,(lambda (x) (pass-select-instructions x)) ,interp-x86-5)
        ("liveness analysis"        ,(lambda (x) (pass-uncover-live x)) ,interp-x86-5)
        ("build interference graph" ,(lambda (x) (pass-build-interference x)) ,interp-x86-5)
        ("allocate registers"       ,(lambda (x) (pass-allocate-registers x)) ,interp-x86-5)
        ("patch instructions"       ,(lambda (x) (pass-patch-instructions x)) ,interp-x86-5)
        ("prelude and conclusion"   ,(lambda (x) (pass-prelude-and-conclusion x)) #f)))))
    
(module* main #f
  (send (new compiler-gradual) run-tests #t))

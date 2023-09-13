#! /usr/bin/env -S nix shell nixpkgs#racket --command racket
#lang racket
(require "compiler-gradual.rkt")
(require "interp-poly.rkt")
(require "type-check-poly.rkt")
(require "interp-Lcast.rkt")
(require "interp-Lcast-prime.rkt")
(require "type-check-gradual.rkt")
(require "type-check-Llambda.rkt")
(require "interp-Cany-proxy.rkt")
(require "utilities.rkt")
(require "interp.rkt")
(provide (all-defined-out))

(define compiler-poly
  (class compiler-gradual
    (inherit
      pass-lower-casts pass-differentiate-proxies pass-shrink pass-uniquify
      pass-reveal-functions pass-reveal-casts pass-convert-assignments
      pass-convert-closures pass-limit-functions pass-expose-allocation
      pass-uncover-get! pass-remove-complex-operands pass-explicate-control pass-remove-dead-blocks
      pass-select-instructions pass-uncover-live pass-build-interference
      pass-allocate-registers pass-patch-instructions pass-prelude-and-conclusion 
      pass-build-dominance pass-convert-to-SSA pass-loop-invariant-code-motion pass-dead-code-elimination pass-convert-from-SSA)
      
    (super-new)
    
    (define/override ((induct-L f) exp)
      (match exp
        [(Inst e t v) (f (Inst ((induct-L f) e) t v))]
        [exp ((super induct-L f) exp)]))
     
    (define/public (pass-erase-types p)
      (define ((subst-type f) t)
        (match t
          [`(,arg-tys ... -> ,rty) `(,@(map (subst-type f) arg-tys) -> ,((subst-type f) rty))]
          [`(Vector ,etys ...) `(Vector ,@(map (subst-type f) etys))]
          [`(All ,ty-vars ,ty)
           (define (new-f t)
             (if (set-member? ty-vars t)
               t
               (f t)))
           `(All ,ty-vars ,((subst-type new-f) ty))]
          [t (f t)]))
   
      (define ((erase-All env) ty)
        (match ty
          [`(,arg-tys ... -> ,rty) `(,@(map (erase-All env) arg-tys) -> ,((erase-All env) rty))]
          [`(Vector ,etys) `(Vector ,@(map (erase-All env) etys))]
          [`(All ,ty-vars ,ty)
           (define new-env
             (for/fold ([new-env env]) ([v ty-vars])
               (set-add new-env v)))
           ((erase-All new-env) ty)]
          [t #:when (set-member? env t) 'Any]
          [t t]))
      
      (define (erase-types-exp env)
        (induct-L
          (match-lambda
            [(Inst e `(All ,ty-vars ,ty) ty-vals)
             (define (env-subst t)
               (if (set-member? env t)
                 'Any
                 t))
             (define (src-subst t)
               (if (set-member? ty-vars t)
                 'Any
                 t))
             (define (tgt-subst t)
               (define m (for/hash ([v ty-vars] [t ty-vals]) (values v t)))
               (dict-ref m t t))
             (define src-ty ((erase-All env) ((subst-type env-subst) ((subst-type src-subst) ty))))
             (define tgt-ty ((erase-All env) ((subst-type env-subst) ((subst-type tgt-subst) ty))))
             (Cast e src-ty tgt-ty)]
            [exp exp])))
         
      (define ((erase-types-def env) def)
        (match def
          [(Poly tyvars def)
           ((erase-types-def (for/fold ([env env]) ([v tyvars]) (set-add env v))) def)]
          [(Def name params rty info body)
           (define (erase t)
             ((erase-All (set))
              ((subst-type (lambda (t) (if (set-member? env t) 'Any t)))
               t)))
           (Def name
             (for/list ([p params])
               (match p
                 [`(,x : ,t) `(,x : ,(erase t))]))
             (erase rty)
             info
             ((erase-types-exp env) body))]))
      
      (match p
        [(Program info exp)
         (Program info (erase-types-exp exp))]
         
        [(ProgramDefsExp info defs exp)
         (ProgramDefsExp info (map (erase-types-def (set)) defs) ((erase-types-exp (set)) exp))]))
         
    (define/override (interp) interp-poly)
    (define/override (type-checker) type-check-poly)
    (define/override (test-specs)
      `(
        (0 "var")
        (0 "cond")
        (0 "while")
        (0 "vectors")
        (0 "functions")
        (0 "lambda")
        (0 "poly")
        (0 "opt")))
             
    (define/override (compiler-passes)
      (define (annotate-var-type e)
        (parameterize ([typed-vars #t])
          (type-check-Lany-proxy e)))
      `(
        ("erase types"                ,(lambda (x) (pass-erase-types x)) ,interp-Lcast ,type-check-gradual)
        ("lower casts"                ,(lambda (x) (pass-lower-casts x)) ,interp-Lcast ,type-check-Lany-proxy)
        ("differentiate proxies"      ,(lambda (x) (pass-differentiate-proxies x)) ,interp-Lcast ,type-check-Lany-proxy)
        ("shrink"                     ,(lambda (x) (pass-shrink x)) ,interp-Lcast ,type-check-Lany-proxy)
        ("uniquify"                   ,(lambda (x) (pass-uniquify x)) ,interp-Lcast ,type-check-Lany-proxy)
        ("reveal FunRef"              ,(lambda (x) (pass-reveal-functions x)) ,interp-Lcast-prime ,type-check-Lany-proxy)
        ("reveal casts"               ,(lambda (x) (pass-reveal-casts x)) ,interp-Lcast-prime ,type-check-Lany-proxy)
        ("convert assignments"        ,(lambda (x) (pass-convert-assignments x)) ,interp-Lcast-prime ,type-check-Lany-proxy)
        ("annotate var types"         ,(lambda (x) x) ,interp-Lcast-prime ,annotate-var-type)
        ("convert closures"           ,(lambda (x) (pass-convert-closures x)) ,interp-Lcast-prime ,type-check-Lany-proxy)
        ("limit funtion parameters"   ,(lambda (x) (pass-limit-functions x)) ,interp-Lcast-prime ,type-check-Lany-proxy)
        ("expose allocation"          ,(lambda (x) (pass-expose-allocation x)) ,interp-Lcast-prime ,type-check-Lany-proxy)
        ("uncover get!"               ,(lambda (x) (pass-uncover-get! x)) ,interp-Lcast-prime ,type-check-Lany-proxy)
        ("remove complex operands"    ,(lambda (x) (pass-remove-complex-operands x)) ,interp-Lcast-prime ,type-check-Lany-proxy)
        ("explicate control"          ,(lambda (x) (pass-explicate-control x)) ,interp-Cany-proxy ,type-check-Cany-proxy)
        ("remove dead blocks"         ,(lambda (x) (pass-remove-dead-blocks x)) ,interp-Cany-proxy ,type-check-Cany-proxy)
        ("build dominance"            ,(lambda (x) (pass-build-dominance x)) ,interp-Cany-proxy ,type-check-Cany-proxy)
        ("convert to SSA"             ,(lambda (x) (pass-convert-to-SSA x)) ,interp-Cany-proxy ,type-check-Cany-proxy)
        ("loop invariant code motion" ,(lambda (x) (pass-loop-invariant-code-motion x)) ,interp-Cany-proxy ,type-check-Cany-proxy)
        ("dead code elimination"      ,(lambda (x) (pass-dead-code-elimination x)) ,interp-Cany-proxy ,type-check-Cany-proxy)
        ("convert from SSA"           ,(lambda (x) (pass-convert-from-SSA x)) ,interp-Cany-proxy ,type-check-Cany-proxy)
        ("instruction selection"      ,(lambda (x) (pass-select-instructions x)) ,interp-x86-5)
        ("liveness analysis"          ,(lambda (x) (pass-uncover-live x)) ,interp-x86-5)
        ("build interference graph"   ,(lambda (x) (pass-build-interference x)) ,interp-x86-5)
        ("allocate registers"         ,(lambda (x) (pass-allocate-registers x)) ,interp-x86-5)
        ("patch instructions"         ,(lambda (x) (pass-patch-instructions x)) ,interp-x86-5)
        ("prelude and conclusion"     ,(lambda (x) (pass-prelude-and-conclusion x)) #f)))))
    
(module* main #f
  (send (new compiler-poly) run-tests #t))

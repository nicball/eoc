#! /usr/bin/env -S nix shell nixpkgs#racket --command racket
#lang racket

(require "utilities.rkt")
(require "interp-Lvar.rkt")
(require "interp-Lif.rkt")
(require "interp-Lwhile.rkt")
(require "interp-Lvec.rkt")
(require "interp-Lfun.rkt")
(require "type-check-Lfun.rkt")
;(require "interp-Cvar.rkt")
(require "interp.rkt")
(require "compiler.rkt")
(AST-output-syntax 'concrete-syntax)

;; all the files in the tests/ directory with extension ".rkt".
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

(debug-level 0)
(interp-tests "var" type-check-Lfun compiler-passes interp-Lfun "var_test" (tests-for "var"))
(interp-tests "cond" type-check-Lfun compiler-passes interp-Lfun "cond_test" (tests-for "cond"))
(interp-tests "while" type-check-Lfun compiler-passes interp-Lfun "while_test" (tests-for "while"))
(interp-tests "vec" type-check-Lfun compiler-passes interp-Lfun "vectors_test" (tests-for "vectors"))
(interp-tests "fun" type-check-Lfun compiler-passes interp-Lfun "functions_test" (tests-for "functions"))

;; Uncomment the following when all the passes are complete to
;; test the final x86 code.
(debug-level 0)
(compiler-tests "var" type-check-Lfun compiler-passes "var_test" (tests-for "var"))
(compiler-tests "cond" type-check-Lfun compiler-passes "cond_test" (tests-for "cond"))
(compiler-tests "while" type-check-Lfun compiler-passes "while_test" (tests-for "while"))
(compiler-tests "vec" type-check-Lfun compiler-passes "vectors_test" (tests-for "vectors"))
(compiler-tests "fun" type-check-Lfun compiler-passes "functions_test" (tests-for "functions"))


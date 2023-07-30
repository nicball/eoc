#! /usr/bin/env -S nix shell nixpkgs#racket --command racket
#lang racket

(require "utilities.rkt")
(require "interp-Lcast.rkt")
(require "type-check-gradual.rkt")
(require "compiler-gradual.rkt")
(AST-output-syntax 'concrete-syntax)

;; all the files in the tests/ directory with extension ".rkt".
(define all-tests
  (let* ([files (directory-list (build-path (current-directory) "tests"))]
         [tyerrs (map (lambda (p) (car (string-split (path->string p) ".")))
                      (filter (lambda (p) (string=? (cadr (string-split (path->string p) ".")) "tyerr"))
                              files))])
    (map (lambda (p) (car (string-split (path->string p) ".")))
         (filter (lambda (p)
                   (and (string=? (cadr (string-split (path->string p) ".")) "rkt")
                        (not (set-member? tyerrs (car (string-split (path->string p) "."))))))
                 files))))

(define (tests-for r)
  (map (lambda (p)
         (caddr (string-split p "_")))
       (filter
        (lambda (p)
          (string=? r (car (string-split p "_"))))
        all-tests)))

(debug-level 1)
;(AST-output-syntax 'abstract-syntax)
(debug-level 0)
(interp-tests "var" type-check-gradual compiler-passes interp-Lcast "var_test" (tests-for "var"))
(interp-tests "cond" type-check-gradual compiler-passes interp-Lcast "cond_test" (tests-for "cond"))
(interp-tests "while" type-check-gradual compiler-passes interp-Lcast "while_test" (tests-for "while"))
(interp-tests "vec" type-check-gradual compiler-passes interp-Lcast "vectors_test" (tests-for "vectors"))
(interp-tests "fun" type-check-gradual compiler-passes interp-Lcast "functions_test" (tests-for "functions"))
(interp-tests "lambda" type-check-gradual compiler-passes interp-Lcast "lambda_test" (tests-for "lambda"))
(interp-tests "gradual" type-check-gradual compiler-passes interp-Lcast "gradual_test" (tests-for "gradual"))

;; Uncomment the following when all the passes are complete to
;; test the final x86 code.
(debug-level 1)
(debug-level 0)
(compiler-tests "var" type-check-gradual compiler-passes "var_test" (tests-for "var"))
(compiler-tests "cond" type-check-gradual compiler-passes "cond_test" (tests-for "cond"))
(compiler-tests "while" type-check-gradual compiler-passes "while_test" (tests-for "while"))
(compiler-tests "vec" type-check-gradual compiler-passes "vectors_test" (tests-for "vectors"))
(compiler-tests "fun" type-check-gradual compiler-passes "functions_test" (tests-for "functions"))
(compiler-tests "gradual" type-check-gradual compiler-passes "gradual_test" (tests-for "gradual"))

#! /usr/bin/env -S nix shell nixpkgs#racket --command racket
#lang racket

(require "utilities.rkt")
(require "interp-Ldyn.rkt")
(require "type-check-Lany.rkt")
(require "compiler-Ldyn.rkt")
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
(interp-tests "var" strip-types compiler-passes interp-Ldyn "var_test" (tests-for "var"))
(interp-tests "cond" strip-types compiler-passes interp-Ldyn "cond_test" (tests-for "cond"))
(interp-tests "while" strip-types compiler-passes interp-Ldyn "while_test" (tests-for "while"))
(interp-tests "vec" strip-types compiler-passes interp-Ldyn "vectors_test" (tests-for "vectors"))
(interp-tests "fun" strip-types compiler-passes interp-Ldyn "functions_test" (tests-for "functions"))
(interp-tests "dynamic" strip-types compiler-passes interp-Ldyn "dynamic_test" (tests-for "dynamic"))

;; Uncomment the following when all the passes are complete to
;; test the final x86 code.
(debug-level 1)
(debug-level 0)
(compiler-tests "var" strip-types compiler-passes "var_test" (tests-for "var"))
(compiler-tests "cond" strip-types compiler-passes "cond_test" (tests-for "cond"))
(compiler-tests "while" strip-types compiler-passes "while_test" (tests-for "while"))
(compiler-tests "vec" strip-types compiler-passes "vectors_test" (tests-for "vectors"))
(compiler-tests "fun" strip-types compiler-passes "functions_test" (tests-for "functions"))
(compiler-tests "dynamic" strip-types compiler-passes "dynamic_test" (tests-for "dynamic"))

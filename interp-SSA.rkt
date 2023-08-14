#! /usr/bin/env -S nix shell nixpkgs#racket --command racket
#lang racket
;; op := add sub neg id? call mul and or sal sar xor cmp funcaddr
;;       store load
;;       return jmp branch tailcall
;; arg := int global var
;; instr := (var op (arg ...))
;;          (phi ((label . var) ...))

;; x = add a1 a2
;; br (eq? cond 1) .then .else
;; 
;; .then
;; x = add x a1
;; jmp .end
;; 
;; .else
;; x = add x a2
;; jmp .end
;; 
;; .end
;; x = phi x x
;; ret x

(require "utilities.rkt")

(struct SsaProgram [info def*])
(struct SsaBlock [info instr*])
(struct SsaInstr [var op arg*])
(struct Phi [var source*])
(struct Branch [cc arg1 arg2 then else])

(define example-program
  (SsaProgram '()
    (list
      (Def 'main '() 'Integer '()
        (hash
          'start
          (SsaBlock '()
            (list
              (SsaInstr 'a1 'id (list (Int 1)))
              (SsaInstr 'a2 'id (list (Int 2)))
              (SsaInstr 'cond 'call (list (Global 'random)))
              (SsaInstr 'x 'add (list (Var 'a1) (Var 'a2)))
              (Branch 'eq? (Var 'cond) (Int 1) 'then 'else)))
          'then
          (SsaBlock '()
            (list
              (SsaInstr 'x 'add (list (Var 'x) (Var 'a1)))
              (Jmp 'end)))
          'else
          (SsaBlock '()
            (list
              (SsaInstr 'x 'add (list (Var 'x) (Var 'a2)))
              (Jmp 'end)))
          'end
          (SsaBlock '()
            (list
              (Phi 'x `((then . ,(Var 'x)) (else . ,(Var 'x))))
              (Return (Var 'x))))))
      (Def 'random '() 'Integer '()
        (hash
          'start
          (SsaBlock '()
            (list
              (Return (Int 1)))))))))

(define interp-SSA-class
  (class object%
         
    (super-new)
         
    (define definitions (make-hash))
    
    (define/public (interp-program prog)
      (match prog
        [(SsaProgram info defs)
         (for ([def (in-list defs)])
           (dict-set! definitions (Def-name def) def))
         (call-function 'main '())]))
    
    (define (call-function name args)
      (match (dict-ref definitions name)
        [(Def name params 'Integer info blocks)
         (assert "wrong number of arguments" (equal? (length args) (length params)))
         (define env
           (for/hash ([n params] [a args]) (values n a)))
         (define lh label-history)
         (define old-blocks current-blocks)
         (set! current-blocks blocks)
         (define res (interp-blocks env blocks))
         (set! label-history lh)
         (set! current-blocks old-blocks)
         res]))
         
    (define current-blocks (hash))

    (define (interp-blocks env blocks)
      (set! current-blocks blocks)
      (define instrs (SsaBlock-instr* (dict-ref blocks 'start)))
      (set-current-block 'start)
      (interp-instrs env instrs))
         
    (define (interp-instrs env instrs)
      (match instrs
        [(cons (Phi x sources) rest)
         #:when (pair? (car sources))
         (define from (get-last-block))
         (define val
           (for/fold ([val #f]) ([src sources] #:when (equal? (car src) from))
             (interp-exp env (cdr src))))
         (interp-instrs (dict-set env x val) rest)]
        [(cons (Phi _ _) rest)
         (interp-instrs env rest)]
        [(cons (SsaInstr x op (list a b)) rest)
         #:when (dict-has-key? binary-ops op)
         (define a-val (interp-exp env a))
         (define b-val (interp-exp env b))
         (interp-instrs (dict-set env x ((dict-ref binary-ops op) a-val b-val)) rest)]
        [(cons (SsaInstr x op (list a)) rest)
         #:when (dict-has-key? unary-ops op)
         (define a-val (interp-exp env a))
         (interp-instrs (dict-set env x ((dict-ref unary-ops op) a-val)) rest)]
        [(cons (SsaInstr x 'call (cons f args)) rest)
         (define name (interp-exp env f))
         (define arg-vals (for/list ([a args]) (interp-exp env a)))
         (define ret (call-function name arg-vals))
         (interp-instrs (dict-set env x ret) rest)]
        [(cons (SsaInstr x 'cmp (list op a b)) rest)
         (define a-val (interp-exp env a))
         (define b-val (interp-exp env b))
         (define res (interp-cmp op a-val b-val))
         (interp-exp (dict-set env x res) rest)]
        [(cons (Return v) rest)
         (interp-exp env v)]
        [(cons (Jmp label) rest)
         (define instrs (SsaBlock-instr* (dict-ref current-blocks label)))
         (set-current-block label)
         (interp-instrs env instrs)]
        [(cons (Branch op a b then else) rest)
         (define a-val (interp-exp env a))
         (define b-val (interp-exp env b))
         (define target (if (zero? (interp-cmp op a-val b-val)) else then))
         (define instrs (SsaBlock-instr* (dict-ref current-blocks target)))
         (set-current-block target)
         (interp-instrs env instrs)]
        [(cons (TailCall f args) rest)
         (define name (interp-exp env f))
         (define arg-vals (for/list ([a args]) (interp-exp env a)))
         (call-function name arg-vals)]))

    (define (interp-exp env exp)
      (match exp
        [(Var x) (dict-ref env x)]
        [(Int n) n]
        [(Global x) x])) ; todo gc

    (define binary-ops
      (hash
        'add +
        'sub -
        'mul *
        'and bitwise-and
        'or bitwise-ior
        'sal arithmetic-shift
        'sar (lambda (x n) (arithmetic-shift x (- n)))
        'xor bitwise-xor))

    (define unary-ops
      (hash
        'neg -
        'id (lambda (x) x)
        'funcaddr (lambda (x) x)))

    (define (interp-cmp op a b)
      (define op-fn
        (match op
          ['eq? equal?]
          ['< <]
          ['<= <=]
          ['> >]
          ['>= >=]))
      (if (op-fn a b) 1 0))

    (define label-history '())
    (define (set-current-block label)
      (set! label-history (cons label label-history))
      (when (> (length label-history) 2)
        (set! label-history (take label-history 2))))
    (define (get-last-block)
      (assert "dangling phi node" (equal? (length label-history) 2))
      (second label-history))))

(send (new interp-SSA-class) interp-program example-program)

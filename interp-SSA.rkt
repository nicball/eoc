#! /usr/bin/env -S nix shell nixpkgs#racket --command racket
#lang racket
;; op := add sub neg id call indirect_call mul and or sal sar xor cmp
;;       load_global func_addr load allocate
;;       store collect
;;       return jmp branch tailcall
;; arg := int var
;; instr := (var op (arg ...))
;;          (phi ((label . var) ...))

;; function main()
;; .start
;; a1 = id 1
;; a2 = id 2
;; cond = call random()
;; x = add a1 a2
;; br (eq? cond 1) .then .else
;; 
;; .then
;; x2 = add x a1
;; jmp .end
;; 
;; .else
;; x3 = add x a2
;; jmp .end
;; 
;; .end
;; x4 = phi .then x2 .else x3
;; vec = allocate 8
;; store x4 vec 0
;; v = load vec 0
;; return v

;; function random()
;; .start
;; return 0

(require "utilities.rkt")

(struct SsaProgram [info def*])
(struct SsaBlock [info instr*])
(struct SsaInstr [var op arg*])
(struct Phi [var source*])
(struct Branch [cc arg1 arg2 then else])
(struct Store [val base offset])

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
              (SsaInstr 'cond 'call (list 'random))
              (SsaInstr 'x 'add (list (Var 'a1) (Var 'a2)))
              (Branch 'eq? (Var 'cond) (Int 1) 'then 'else)))
          'then
          (SsaBlock '()
            (list
              (SsaInstr 'x2 'add (list (Var 'x) (Var 'a1)))
              (Jmp 'end)))
          'else
          (SsaBlock '()
            (list
              (SsaInstr 'x3 'add (list (Var 'x) (Var 'a2)))
              (Jmp 'end)))
          'end
          (SsaBlock '()
            (list
              (Phi 'x4 `((then . ,(Var 'x2)) (else . ,(Var 'x3))))
              (SsaInstr 'vec 'allocate (list (Int 8)))
              (Store (Var 'x4) (Var 'vec) 0)
              (SsaInstr 'v 'load (list (Var 'vec) (Int 0)))
              (Return (Var 'v))))))
      (Def 'random '() 'Integer '()
        (hash
          'start
          (SsaBlock '()
            (list
              (Return (Int 0)))))))))

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
        [(cons (SsaInstr x 'func_addr (list name)) rest)
         (interp-instrs (dict-set env x name) rest)]
        [(cons (SsaInstr x 'load_global (list name)) rest)
         (define val
           (match name
             ['free_ptr 0]
             ['fromspace_end 640000]))
         (interp-instrs (dict-set env x val) rest)]
        [(cons (SsaInstr x 'load (list a (Int offset))) rest)
         (define addr (+ (interp-exp env a) offset))
         (define val (read-memory addr))
         (interp-instrs (dict-set env x val) rest)]
        [(cons (SsaInstr x 'allocate (list (Int size))) rest)
         (define val (allocate-memory! size))
         (interp-instrs (dict-set env x val) rest)] 
        [(cons (Store v base offset) rest)
         (define val (interp-exp env v))
         (define addr (+ (interp-exp env base) offset))
         (write-memory! addr val)
         (interp-instrs env rest)]
        [(cons (Collect _) rest)
         (interp-instrs env rest)]
        [(cons (SsaInstr x 'call (cons name args)) rest)
         (define arg-vals (for/list ([a args]) (interp-exp env a)))
         (define ret (call-function name arg-vals))
         (interp-instrs (dict-set env x ret) rest)]
        [(cons (SsaInstr x 'indirectcall (cons f args)) rest)
         (define name (interp-exp env f))
         (define arg-vals (for/list ([a args]) (interp-exp env a)))
         (define ret (call-function name arg-vals))
         (interp-instrs (dict-set env x ret) rest)]
        [(cons (SsaInstr x 'cmp (list op a b)) rest)
         (define a-val (interp-exp env a))
         (define b-val (interp-exp env b))
         (define res (interp-cmp op a-val b-val))
         (interp-instrs (dict-set env x res) rest)]
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
        [(Int n) n]))

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
        'id (lambda (x) x)))
         
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
      (second label-history))

    (define max-memory-addr 0)
         
    (define memory-objects (make-hash))
         
    (define (allocate-memory! size)
      (define ptr (+ max-memory-addr 100))
      (set! max-memory-addr (+ ptr size))
      (define num-elem (/ size 8))
      (define v (make-vector num-elem #f))
      (dict-set! memory-objects ptr (list size v))
      ptr)

    (define (read-memory ptr)
      (define val #f)
      (for ([(base alloc) (in-dict memory-objects)]
            #:when (and (<= base ptr) (< ptr (+ base (car alloc)))))
        #:final #t
        (define index (/ (- ptr base) 8))
        (set! val (vector-ref (cadr alloc) index)))
      (assert "memory read invalid" val)
      val)

    (define (write-memory! ptr val)
      (define written #f)
      (for ([(base alloc) (in-dict memory-objects)]
            #:when (and (<= base ptr) (< ptr (+ base (car alloc)))))
        #:final #t
        (define index (/ (- ptr base) 8))
        (vector-set! (cadr alloc) index val)
        (set! written #t))
      (assert "memory write invalid" written)
      val)))

(send (new interp-SSA-class) interp-program example-program)

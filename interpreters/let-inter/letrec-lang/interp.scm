(module interp (lib "eopl.ss" "eopl")
  
  ;; cps interpreter for the LETREC language, using the data structure
  ;; representation of continuations (Figure 5.3).

  ;; exercise: rewrite this using the procedural representation of
  ;; continuations (Figure 5.2).

  ;; exercise: rewrite this using a trampoline (page 159).

  (require "drscheme-init.scm")

  (require "lang.scm")
  (require "data-structures.scm")
  (require "environments.scm")

  (provide value-of-program value-of/k)

;;;;;;;;;;;;;;;; the interpreter ;;;;;;;;;;;;;;;;

  ;; value-of-program : Program -> FinalAnswer
  ;; Page: 143 and 154
  (define value-of-program 
    (lambda (pgm)
      (cases program pgm
        (a-program (exp1)
          (value-of/k exp1 (init-env) (end-cont))))))  

  ;; value-of/k : Exp * Env * Cont -> FinalAnswer
  ;; Page: 143--146, and 154
  (define value-of/k
    (lambda (exp env cont)
      (cases expression exp
        (const-exp (num) (apply-cont cont (num-val num)))
        (var-exp (var) (apply-cont cont (apply-env env var)))
        (proc-exp (var body)
          (apply-cont cont 
            (proc-val (procedure var body env))))
        (letrec-exp (p-name b-var p-body letrec-body)
          (value-of/k letrec-body
            (extend-env-rec p-name b-var p-body env)
            cont))
        (zero?-exp (exp1)
          (value-of/k exp1 env
            (zero1-cont cont)))
        (let-exp (var exp1 body)
          (value-of/k exp1 env
            (let-exp-cont var body env cont)))
        (if-exp (exp1 exp2 exp3)
          (value-of/k exp1 env
            (if-test-cont exp2 exp3 env cont)))
        (diff-exp (exp1 exp2)
          (value-of/k exp1 env
            (diff1-cont exp2 env cont)))        
        (call-exp (rator rand) 
          (value-of/k rator env
            (rator-cont rand env cont)))
   )))

  ;; apply-cont : Cont * ExpVal -> FinalAnswer
  ;; Page: 148
  (define apply-cont
    (lambda (cont val)
      (cont val)))

;;;;;;;;;;;; Continuations ;;;;;;;;;;;;;;
  (define end-cont
    (lambda ()
      (lambda (val)
        (begin
          (eopl:printf "end of computation ~%")
          val))))

  (define zero1-cont
    (lambda (cont)
      (lambda (val)
        (apply-cont cont (bool-val (zero? (expval->num val)))))
      ))

  (define let-exp-cont
    (lambda (var body env cont)
      (lambda (val)
        (value-of/k body (extend-env var val env) cont))))

  (define if-test-cont
    (lambda (exp2 exp3 env cont)
      (lambda (val)
        (if (expval->bool val)
          (value-of/k exp2 env cont)
          (value-of/k exp3 env cont)))))

  (define diff1-cont
    (lambda (exp3 env cont)
      (lambda (val)
        (value-of/k exp3 env (diff2-cont val cont)))))

  (define diff2-cont
    (lambda (val1 cont)
      (lambda (val2)
        (let ((num1 (expval->num val1))
              (num2 (expval->num val2)))
          (apply-cont cont (num-val (- num1 num2)))))))

  (define rator-cont
    (lambda (rand env cont)
      (lambda (val)
        (value-of/k rand env (rand-cont val cont)))))

  (define rand-cont
    (lambda (pro cont)
      (lambda (val)
        (let ((proc (expval->proc pro)))
          (apply-procedure/k proc val cont)))))

  ;; apply-procedure/k : Proc * ExpVal * Cont -> FinalAnswer
  ;; Page 152 and 155
  (define apply-procedure/k
    (lambda (proc1 arg cont)
      (cases proc proc1
        (procedure (var body saved-env)
          (value-of/k body
            (extend-env var arg saved-env)
            cont)))))
  
  )
  


  

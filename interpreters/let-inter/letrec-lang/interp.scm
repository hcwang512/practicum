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
        (let-exp (vars exps body)
          (value-of/k (car exps) env
            (let-exp-cont (car vars) (cdr vars) (cdr exps) body env cont)))
        (if-exp (exp1 exp2 exp3)
          (value-of/k exp1 env
            (if-test-cont exp2 exp3 env cont)))
        (diff-exp (exp1 exp2)
          (value-of/k exp1 env
            (diff1-cont exp2 env cont)))        
        (emptylist-exp ()
          (apply-cont cont (emptylist-val)))
        (null?-exp (exp1)
          (value-of/k exp1 env (null?-cont cont)))
        (cons-exp (exp1 exp2)
          (value-of/k exp1 env (cons1-cont exp2 env cont)))
        (car-exp (exp1)
          (value-of/k exp1 env (car-cont cont)))
        (cdr-exp (exp1)
          (value-of/k exp1 env (cdr-cont cont)))
        (list-exp (exps)
          (if (null? exps)
            (apply-cont (list-cont exps env cont) exps)
            (value-of/k (car exps) env (list-cont (cdr exps) env cont))))
        (call-exp (rator rand) 
          (value-of/k rator env
            (rator-cont rand env cont)))
   )))

  ;; apply-cont : Cont * ExpVal -> FinalAnswer
  ;; Page: 148
  (define apply-cont
    (lambda (cont val)
      (cases continuation cont
        (end-cont () 
          (begin
            (eopl:printf
              "End of computation.~%")
            val))
        ;; or (logged-print val)  ; if you use drscheme-init-cps.scm
        (zero1-cont (saved-cont)
          (apply-cont saved-cont
            (bool-val
              (zero? (expval->num val)))))
        (let-exp-cont (var vars exps body saved-env saved-cont)
          (if (null? vars) (value-of/k body (extend-env var val saved-env) saved-cont)
            (value-of/k (car exps) saved-env (let-exp-cont (car vars) (cdr vars) (cdr exps) body (extend-env var val saved-env) saved-cont))))
        (if-test-cont (exp2 exp3 saved-env saved-cont)
          (if (expval->bool val)
             (value-of/k exp2 saved-env saved-cont)
             (value-of/k exp3 saved-env saved-cont)))
        (diff1-cont (exp2 saved-env saved-cont)
          (value-of/k exp2
            saved-env (diff2-cont val saved-cont)))
        (diff2-cont (val1 saved-cont)
          (let ((num1 (expval->num val1))
                (num2 (expval->num val)))
            (apply-cont saved-cont
              (num-val (- num1 num2)))))
        (null?-cont (saved-cont)
          (apply-cont saved-cont (expval-null? val)))
        (cons1-cont (exp2 env saved-cont)
          (value-of/k exp2 env (cons2-cont val saved-cont)))
        (cons2-cont (val1 saved-cont)
          (apply-cont saved-cont (pair-val val1 (pair-val val (emptylist-val)))))
        (car-cont (saved-cont)
          (let ((car-val (expval->car val)))
            (apply-cont saved-cont car-val)))
        (cdr-cont (saved-cont)
          (let ((cdr-val (expval->cdr val)))
            (apply-cont saved-cont cdr-val)))
        (list-cont (exps saved-env saved-cont)
          (if (null? exps) (apply-cont saved-cont (emptylist-val))
            (value-of/k (car exps) saved-env (list1-cont (cdr exps) (list val) saved-env saved-cont))))
        (list1-cont (exps vals saved-env saved-cont)
          (if (null? exps)
            (apply-cont saved-cont (vals->pair (append vals (list val))))
            (value-of/k (car exps) saved-env (list1-cont (cdr exps) (append vals (list val)) saved-env saved-cont))))
        (rator-cont (rand saved-env saved-cont)
          (value-of/k rand saved-env
            (rand-cont val saved-cont)))
        (rand-cont (val1 saved-cont)
          (let ((proc (expval->proc val1)))
            (apply-procedure/k proc val saved-cont)))
        )))

  (define vals->pair
    (lambda (vals)
      (if (null? vals) (emptylist-val)
        (pair-val (car vals) (vals->pair (cdr vals))))))

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
  


  

(module interp (lib "eopl.ss" "eopl")
  
  ;; interpreter for the IMPLICIT-REFS language

  (require "drscheme-init.scm")

  (require "lang.scm")
  (require "data-structures.scm")
  (require "environments.scm")
  (require "store.scm")
  
  (provide value-of-program value-of instrument-let instrument-newref)

;;;;;;;;;;;;;;;; switches for instrument-let ;;;;;;;;;;;;;;;;

  (define instrument-let (make-parameter #f))

  ;; say (instrument-let #t) to turn instrumentation on.
  ;;     (instrument-let #f) to turn it off again.

;;;;;;;;;;;;;;;; the interpreter ;;;;;;;;;;;;;;;;

  ;; value-of-program : Program -> ExpVal
  (define value-of-program 
    (lambda (pgm)
      (initialize-store!)
      (cases program pgm
        (a-program (exp1)
          (result-of exp1 (init-env))))))

  (define extend-unset-env*
    (lambda (vars env)
      (if (null? vars) env
        (extend-unset-env* (cdr vars) (extend-env (car vars) (newref 1) #f env)))))

  (define execute-while
    (lambda (cond-exp body env)
      (when (expval->bool (value-of cond-exp env))
        (begin
          (result-of body env)
          (execute-while cond-exp body env))
        )))

  (define result-of
    (lambda (stat env)
      (cases statement stat
        (assign-stat (var exp1)
          (setref! (apply-env env var #f) (value-of exp1 env)))
        (print-stat (exp1)
            (eopl:printf "print: ~s" (value-of exp1 env)))
        (declare-stat (vars body)
          (result-of body (extend-unset-env* vars env)))
        (while-stat (cond-exp body)
          (execute-while cond-exp body env))
        (if-stat (cond-exp stat1 stat2)
          (if (expval->bool (value-of cond-exp env))
            (result-of stat1 env)
            (result-of stat2 env)))
        (block-stat (stats)
          (results-of stats env)))))

  (define results-of
    (lambda (stats env)
      (when (not (null? stats))
        (begin
          (result-of (car stats) env)
          (results-of (cdr stats) env)))))

  ;; value-of : Exp * Env -> ExpVal
  ;; Page: 118, 119
  (define value-of
    (lambda (exp env)
      (cases expression exp

        ;\commentbox{ (value-of (const-exp \n{}) \r) = \n{}}
        (const-exp (num) (num-val num))

        ;\commentbox{ (value-of (var-exp \x{}) \r) 
        ;              = (deref (apply-env \r \x{}))}
        (var-exp (var) (deref (apply-env env var #f)))

        ;\commentbox{\diffspec}
        (diff-exp (exp1 exp2)
          (let ((val1 (value-of exp1 env))
                (val2 (value-of exp2 env)))
            (let ((num1 (expval->num val1))
                  (num2 (expval->num val2)))
              (num-val
                (- num1 num2)))))

        ;\commentbox{\zerotestspec}
        (zero?-exp (exp1)
          (let ((val1 (value-of exp1 env)))
            (let ((num1 (expval->num val1)))
              (if (zero? num1)
                (bool-val #t)
                (bool-val #f)))))
              
        ;\commentbox{\ma{\theifspec}}
        (if-exp (exp1 exp2 exp3)
          (let ((val1 (value-of exp1 env)))
            (if (expval->bool val1)
              (value-of exp2 env)
              (value-of exp3 env))))

        ;\commentbox{\ma{\theletspecsplit}}
        (let-exp (vars exps body)       
          (let ((v1 (map (lambda (ele) (value-of ele env)) exps)))
            (value-of body
              (extend-env* vars (map (lambda (ele) (newref ele)) v1) #f env))))
        
        (letmutable-exp (vars exps body)       
          (let ((v1 (map (lambda (ele) (value-of ele env)) exps)))
            (value-of body
              (extend-env* vars (map (lambda (ele) (newref ele)) v1) #t env))))

        (proc-exp (vars body)
          (proc-val (procedure vars body env)))

        (call-exp (rator rands)
          (let ((proc (expval->proc (value-of rator env)))
                (args (map (lambda (ele) (value-of ele env)) rands)))
            (apply-procedure proc args)))

        (letrec-exp (p-names b-vars-list p-bodies letrec-body)
          (value-of letrec-body
            (extend-env-rec* p-names b-vars-list p-bodies env)))

        (begin-exp (exp1 exps)
          (letrec 
            ((value-of-begins
               (lambda (e1 es)
                 (let ((v1 (value-of e1 env)))
                   (if (null? es)
                     v1
                     (value-of-begins (car es) (cdr es)))))))
            (value-of-begins exp1 exps)))

        (setdynamic-exp (var exp1 body)
          (let ((arg (value-of exp1 env))
                (original-v (deref (apply-env env var #f))))
            (begin
              (setref! (apply-env env var #f) arg)
              (let ((re (value-of body env)))
                (setref! (apply-env env var #f) original-v)
                re))))

        (assign-exp (var exp1)
          (begin
            (setref!
              (apply-env env var #t)
              (value-of exp1 env))
            (num-val 27)))

        )))


  ;; apply-procedure : Proc * ExpVal -> ExpVal
  ;; Page: 119

  ;; uninstrumented version
  ;;  (define apply-procedure
  ;;    (lambda (proc1 val)
  ;;      (cases proc proc1
  ;;        (procedure (var body saved-env)
  ;;          (value-of body
  ;;            (extend-env var (newref val) saved-env))))))
  
  ;; instrumented version
  (define apply-procedure
    (lambda (proc1 args)
      (cases proc proc1
        (procedure (vars body saved-env)
          (let ((r (map (lambda (ele) (newref ele)) args)))
            (let ((new-env (extend-env* vars r #t saved-env)))
              (when (instrument-let)
                (begin
                  (eopl:printf
                    "entering body of proc ~s with env =~%"
                    args)
                  (pretty-print (env->list new-env)) 
                  (eopl:printf "store =~%")
                  (pretty-print (store->readable (get-store-as-list)))
                  (eopl:printf "~%")))
              (value-of body new-env)))))))  

  ;; store->readable : Listof(List(Ref,Expval)) 
  ;;                    -> Listof(List(Ref,Something-Readable))
  (define store->readable
    (lambda (l)
      (map
        (lambda (p)
          (list
            (car p)
            (expval->printable (cadr p))))
        l)))

  )
  


  

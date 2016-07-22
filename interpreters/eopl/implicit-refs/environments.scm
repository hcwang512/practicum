(module environments (lib "eopl.ss" "eopl") 
  
  (require "data-structures.scm")
  (require "store.scm")
  (provide init-env empty-env extend-env apply-env extend-env*)

;;;;;;;;;;;;;;;; initial environment ;;;;;;;;;;;;;;;;
  
  ;; init-env : () -> Env
  ;; (init-env) builds an environment in which:
  ;; i is bound to a location containing the expressed value 1, 
  ;; v is bound to a location containing the expressed value 5, and 
  ;; x is bound to a location containing the expressed value 10.  
  (define init-env 
    (lambda ()
      (extend-env 
        'i (newref (num-val 1)) #t
        (extend-env
          'v (newref (num-val 5)) #t
          (extend-env
            'x (newref (num-val 10)) #t
            (empty-env))))))

;;;;;;;;;;;;;;;; environment constructors and observers ;;;;;;;;;;;;;;;;

  (define apply-env
    (lambda (env search-var write?)
      (cases environment env
        (empty-env ()
          (eopl:error 'apply-env "No binding for ~s" search-var))
        (extend-env (bvar bval mutable? saved-env)
	  (if (eqv? search-var bvar)
        (if (or (not write?) mutable?) bval
          (eopl:error 'apply-env "can not write to unmutable var"))
	    (apply-env saved-env search-var write?)))
        (extend-env-rec* (p-names b-vars p-bodies saved-env)
          (let ((n (location search-var p-names)))
            ;; n : (maybe int)
            (if n
              (newref
                (proc-val
                  (procedure 
                    (list-ref b-vars n)
                    (list-ref p-bodies n)
                    env)))
              (apply-env saved-env search-var write?)))))))

  (define extend-env*
    (lambda (vars exps mutable? env)
      (if (null? vars) env
        (extend-env* (cdr vars) (cdr exps) mutable? (extend-env (car vars) (car exps) mutable? env)))))

  ;; location : Sym * Listof(Sym) -> Maybe(Int)
  ;; (location sym syms) returns the location of sym in syms or #f is
  ;; sym is not in syms.  We can specify this as follows:
  ;; if (memv sym syms)
  ;;   then (list-ref syms (location sym syms)) = sym
  ;;   else (location sym syms) = #f
  (define location
    (lambda (sym syms)
      (cond
        ((null? syms) #f)
        ((eqv? sym (car syms)) 0)
        ((location sym (cdr syms))
         => (lambda (n) 
              (+ n 1)))
        (else #f))))

  )

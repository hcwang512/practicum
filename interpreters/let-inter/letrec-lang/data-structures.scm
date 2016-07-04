(module data-structures (lib "eopl.ss" "eopl")

  (require "lang.scm")                  ; for expression?

  (provide (all-defined-out))               ; too many things to list

;;;;;;;;;;;;;;;; expressed values ;;;;;;;;;;;;;;;;

;;; an expressed value is either a number, a boolean or a procval.

  (define-datatype expval expval?
    (num-val
      (value number?))
    (bool-val
      (boolean boolean?))
    (proc-val 
      (proc proc?))
    (pair-val
      (car expval?)
      (cdr expval?))
    (emptylist-val))

;;; extractors:

  (define expval->num
    (lambda (v)
      (cases expval v
	(num-val (num) num)
	(else (expval-extractor-error 'num v)))))

  (define expval->bool
    (lambda (v)
      (cases expval v
	(bool-val (bool) bool)
	(else (expval-extractor-error 'bool v)))))

  (define expval->proc
    (lambda (v)
      (cases expval v
	(proc-val (proc) proc)
	(else (expval-extractor-error 'proc v)))))

  (define expval->car
    (lambda (v)
      (cases expval v
        (pair-val (car-val cdr-val) car-val)
        (else (expval-extractor-error 'proc v)))))

  (define expval->cdr
    (lambda (v)
      (cases expval v
        (pair-val (car-val cdr-val) cdr-val)
        (else (expval-extractor-error 'proc v)))))

  (define expval-null?
    (lambda (v)
      (cases expval v
        (emptylist-val () (bool-val #t))
        (else (bool-val #f)))))

  (define expval-extractor-error
    (lambda (variant value)
      (eopl:error 'expval-extractors "Looking for a ~s, found ~s"
	variant value)))

;;;;;;;;;;;;;;;; continuations ;;;;;;;;;;;;;;;;

  ;; Page: 148
  (define identifier? symbol?)

  (define-datatype continuation continuation?
    (end-cont)                 
    (zero1-cont
      (saved-cont continuation?))
    (let-exp-cont
      (var identifier?)
      (vars (list-of identifier?))
      (exps (list-of expression?))
      (body expression?)
      (saved-env environment?)
      (saved-cont continuation?))
    (if-test-cont 
      (exp2 expression?)
      (exp3 expression?)
      (saved-env environment?)
      (saved-cont continuation?))
    (diff1-cont                
      (exp2 expression?)
      (saved-env environment?)
      (saved-cont continuation?))
    (diff2-cont                
      (val1 expval?)
      (saved-cont continuation?))
    (rator-cont            
      (rand (list-of expression?))
      (saved-env environment?)
      (saved-cont continuation?))
    (rand-cont             
      (val1 expval?)
      (rand-vals (list-of expval?))
      (rands (list-of expression?))
      (saved-env environment?)
      (saved-cont continuation?))
    (null?-cont
      (saved-cont continuation?))
    (cons1-cont
      (exp2 expression?)
      (env environment?)
      (saved-cont continuation?))
    (cons2-cont
      (val1 expval?)
      (saved-cont continuation?))
    (car-cont
      (saved-cont continuation?))
    (cdr-cont
      (saved-cont continuation?))
    (list-cont
      (exps (list-of expression?))
      (saved-env environment?)
      (saved-cont continuation?))
    (list1-cont
      (exps (list-of expression?))
      (vals (list-of expval?))
      (saved-env environment?)
      (saved-cont continuation?)))

;;;;;;;;;;;;;;;; procedures ;;;;;;;;;;;;;;;;

  (define-datatype proc proc?
    (procedure
      (bvar (list-of symbol?))
      (body expression?)
      (env environment?)))
  
;;;;;;;;;;;;;;;; environment structures ;;;;;;;;;;;;;;;;

  (define-datatype environment environment?
    (empty-env)
    (extend-env 
      (bvar symbol?)
      (bval expval?)
      (saved-env environment?))
    (extend-env-rec
      (p-name symbol?)
      (b-vars (list-of symbol?))
      (p-body expression?)
      (saved-env environment?)))

)

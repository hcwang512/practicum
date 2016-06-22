(load-relative "./libs/init.scm")
(load-relative "./base/environments.scm")

;; replace proc-exp with let-proc-exp
;;

(define the-lexical-spec
  '((whitespace (whitespace) skip)
    (comment ("%" (arbno (not #\newline))) skip)
    (identifier
     (letter (arbno (or letter digit "_" "-" "?")))
     symbol)
    (number (digit (arbno digit)) number)
    (number ("-" digit (arbno digit)) number)
    ))

(define the-grammar
  '((program (expression) a-program)
    (expression (number) const-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression (identifier) var-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    (expression ("proc" "(" (separated-list identifier ",") ")" expression) proc-exp)
    (expression ("letproc" identifier "=" "(" (separated-list identifier ",") ")" expression "in" expression) let-proc-exp)
    (expression ("letrec" identifier "(" (separated-list identifier ",") ")" "=" expression "in" expression) letrec-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
    ))

  ;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;
(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

;;; datetype ;;;
(define-datatype expression expression?
  (var-exp
   (id symbol?))
  (const-exp
   (num number?))
  (zero?-exp
   (expr expression?))
  (if-exp
   (predicate-exp expression?)
   (true-exp expression?)
   (false-exp expression?))
  (diff-exp
   (exp1 expression?)
   (exp2 expression?))
  (let-exp
   (vars (list-of symbols?))
   (vals (list-of expression?))
   (body expression?))
  (proc-exp
    (vars (list-of symbols?))
    (body expression?))
  (let-proc-exp
    (name identifier?)
    (paras (list-of symbol?))
    (body expression?)
    (let-body expression?))
  (letrec-exp
    (name identifier?)
    (params (list-of symbol?))
    (body expression?)
    (let-body expression?))
  (call-exp
   (rator expression?)
   (rands (list-of expression?))))


;;; an expressed value is either a number, a boolean or a procval.
(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (proc-val
   (proc proc?)))

;; proc? : SchemeVal -> Bool
;; procedure : Var * Exp * Env -> Proc
(define-datatype proc proc?
  (procedure
   (vars (list-of symbol?))
   (body expression?)
   (env environment?)))


;;; extractors:
;; expval->num : ExpVal -> Int
(define expval->num
  (lambda (v)
    (cases expval v
	   (num-val (num) num)
	   (else (expval-extractor-error 'num v)))))

;; expval->bool : ExpVal -> Bool
(define expval->bool
  (lambda (v)
    (cases expval v
	   (bool-val (bool) bool)
	   (else (expval-extractor-error 'bool v)))))

;; expval->proc : ExpVal -> Proc
(define expval->proc
  (lambda (v)
    (cases expval v
	   (proc-val (proc) proc)
	   (else (expval-extractor-error 'proc v)))))

(define expval-extractor-error
  (lambda (variant value)
    (error 'expval-extractors "Looking for a ~s, found ~s"
		variant value)))

(define apply-elem
  (lambda (env)
    (lambda (elem)
      (value-of elem env))))

(define extend-env-inter
  (lambda (vars vals env)
    (cond
      ((null? vars) env)
      (else (extend-env-inter (cdr vars) (cdr vals) (extend-env (car vars) (car vals ) env))))))

(define extend-proc-env
  (lambda (a-proc new-env)
    (cases proc a-proc
      (procedure (vars body env) (proc-val (procedure vars body new-env))))))
(define extend-env-rec
  (lambda (name params body env)
    (extend-env name (proc-val (procedure params body env)) env)))

(define apply-env-rec
  (lambda (env search-sym)
    (if (null? env) (error "No binding for ~s" search-sym)
      (let ((sym (extended-env-record->sym env))
            (val (extended-env-record->val env))
            (old-env (extended-env-record->old-env env)))
        (if (eqv? search-sym sym)
          (cases expval val
                 (proc-val (proc) (extend-proc-env proc env))
                 (else val))
          (apply-env-rec old-env search-sym))))))

;; apply-procedure : Proc * ExpVal -> ExpVal
;; Page: 79
(define apply-procedure
  (lambda (proc1 vals)
    (cases proc proc1
           (procedure (vars body saved-env)
                      (value-of body (extend-env-inter vars vals saved-env))))))

;;;;;;;;;;;;;;;; the interpreter ;;;;;;;;;;;;;;;;
;; value-of-program : Program -> ExpVal
(define value-of-program
  (lambda (pgm)
    (cases program pgm
	   (a-program (exp1)
		      (value-of exp1 (init-env))))))

;; value-of : Exp * Env -> ExpVal
(define value-of
  (lambda (exp env)
    (cases expression exp
	   (const-exp (num) (num-val num))
	   (var-exp (var) (apply-env-rec env var))
	   (diff-exp (exp1 exp2)
		     (let ((val1 (value-of exp1 env))
			   (val2 (value-of exp2 env)))
		       (let ((num1 (expval->num val1))
			     (num2 (expval->num val2)))
			 (num-val
			  (- num1 num2)))))

	   (zero?-exp (exp1)
		      (let ((val1 (value-of exp1 env)))
			(let ((num1 (expval->num val1)))
			  (if (zero? num1)
			      (bool-val #t)
			      (bool-val #f)))))

	   (if-exp (exp1 exp2 exp3)
		   (let ((val1 (value-of exp1 env)))
		     (if (expval->bool val1)
			 (value-of exp2 env)
			 (value-of exp3 env))))

	   (let-exp (var exp1 body)
		    (let ((val1 (value-of exp1 env)))
		      (value-of body
				(extend-env var val1 env))))
       (proc-exp (vars body)
            (proc-val (procedure vars body env)))

       (let-proc-exp (name params body let-body)
            (let ((proc (proc-val (procedure params body env))))
              (value-of let-body (extend-env name proc env))))

       (letrec-exp (name params body let-body)
            (value-of let-body (extend-env-rec name params body env)))

	   (call-exp (rator rands)
		     (let ((proc (expval->proc (value-of rator env)))
			   (args (map (apply-elem env) rands )))
		       (apply-procedure proc args)))
	   )))


;; run : String -> ExpVal
(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

(run "(proc(x) -(x,1)  30)")
;(num-val 29)
(run "let x = 3 in -(x,1)")
;(num-val 2)

(run "letproc f = (x) -(x, 1) in (f 30)")
;(num-val 29)
;
(run "(proc(x, y) -(x, y) 10 20)") 
;(num-val -10)

 (run "letrec time(x, y)  = if zero?(x) then 0 else -((time -(x,1)  y), -(0, y)) in (time 3 2)")
;(num-val 6)

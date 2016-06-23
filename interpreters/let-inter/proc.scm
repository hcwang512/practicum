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
    (expression ("letrec" (arbno identifier "(" (separated-list identifier ",") ")" "=" expression) "in" expression) letrec-exp)
    (expression ("(" expression (arbno expression) ")") call-exp)
    ))

  ;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;
(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

;;; datetype ;;;
(define-datatype environment environment?
  (empty-env)
  (extend-env
    (var symbol?)
    (val expval?)
    (saved-env environment?))
  (extend-env-rec
    (names (list-of symbol?))
    (params (list-of (list-of symbol?)))
    (bodys (list-of expression?))
    (saved-env environment?)))

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

(define search-env-rec
  (lambda (search-sym vars params-list bodys saved-env env)
    (cond
      ((null? vars) #f)
      ((eqv? (car vars) search-sym) (proc-val (procedure (car params-list) (car bodys) env)))
      (else (search-env-rec search-sym (cdr vars) (cdr params-list) (cdr bodys) saved-env env)))
      ))
(define apply-env
  (lambda (env search-sym)
    (cases environment env
      (empty-env () (error "No bindings for ~s" search-sym))
      (extend-env (var val saved-env)
        (if (eqv? var search-sym) val (apply-env saved-env search-sym)))
      (extend-env-rec (names params-list bodys saved-env)
        (if (eq? #f (search-env-rec search-sym names params-list bodys saved-env env)) (apply-env saved-env search-sym) 
          (search-env-rec search-sym names params-list bodys saved-env env))))))


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
	   (var-exp (var) (apply-env env var))
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
              (value-of let-body (extend-env-rec (list name) (list params) (list body)  env) )))

       (letrec-exp (names params-list bodys let-body)
            (value-of let-body (extend-env-rec names params-list bodys env)))

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

(run "letrec one(x, y) = if zero?(x) then 1 else (two -(x, 1) y) two(x, y) = if zero?(y) then 0 else (one x -(y , 1)) in (two 5 4)")
;(num-val 0)

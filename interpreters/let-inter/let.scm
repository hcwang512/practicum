;From https://github.com/chenyukang/eopl
(load-relative "./libs/init.scm")
(load-relative "./base/environments.scm")


;;;;;;;;;;;;;;;; grammatical specification ;;;;;;;;;;;;;;;;
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
    (expression (identifier) var-exp)
    (expression (number) const-exp)
    (expression ("-" "(" expression "," expression ")") diff-exp)
    (expression ("+" "(" expression "," expression ")") add-exp)
    (expression ("*" "(" expression "," expression ")") mult-exp)
    (expression ("/" "(" expression "," expression ")") div-exp)
    (expression ("minus" "(" expression ")") minus-exp)
    (expression ("equal?" "(" expression "," expression ")") equal-exp)
    (expression ("greater?" "(" expression "," expression ")") greater-exp)
    (expression ("less?" "(" expression "," expression ")") less-exp)
    (expression ("zero?" "(" expression ")") zero?-exp)
    (expression ("cons" "(" expression "," expression ")") cons-exp)
    (expression ("car" "(" expression ")") car-exp)
    (expression ("cdr" "(" expression ")") cdr-exp)
    (expression ("empty-list") empty-list-exp)
    (expression ("null?" "(" expression ")") null?-exp)
    (expression ("list" "(" (separated-list expression ",")")") list-exp)
    (expression ("cond" (arbno expression "==>" expression) "end" ) cond-exp)
    (expression ("if" expression "then" expression "else" expression) if-exp)
    (expression ("let" identifier "=" expression "in" expression) let-exp)
    ))

;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;
(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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
  (minus-exp
   (body-exp expression?))
  (add-exp
    (exp1 expression?)
    (exp2 expression?))
  (mult-exp
    (exp1 expression?)
    (exp2 expression?))
  (div-exp
    (exp1 expression?)
    (exp2 expression?))
  (diff-exp
   (exp1 expression?)
   (exp2 expression?))
  (equal-exp
    (exp1 expression?)
    (exp2 expression?))
  (greater-exp
    (exp1 expression?)
    (exp2 expression?))
  (cons-exp
    (exp1 expression?)
    (exp2 expression?))
  (car-exp
    (exp expression?))
  (cdr-exp
    (body expression?))
  (empty-list-exp)
  (null?-exp
    (exp expression?))
  (list-exp
    (args (list-of expression?)))
  (cond-exp
    (conds (list-of expression?))
    (acts (list-of expression?)))
  (less-exp
    (exp1 expression?)
    (exp2 expression?))
  (let-exp
   (var symbol?)
   (value expression?)
   (body expression?)))

;;; an expressed value is either a number, a boolean or a procval.
(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (pair-val
    (car expval?)
    (cdr expval?))
  (empty-list-val))

;;; extractors:

;; expval->num : ExpVal -> Int
;; Page: 70
(define expval->num
  (lambda (v)
    (cases expval v
           (num-val (num) num)
           (else (expval-extractor-error 'num v)))))

;; expval->bool : ExpVal -> Bool
;; Page: 70
(define expval->bool
  (lambda (v)
    (cases expval v
           (bool-val (bool) bool)
           (else (expval-extractor-error 'bool v)))))

(define expval->pair
  (lambda (v)
    (cases expval v
           (pair-val (car cdr) (cons car cdr))
           (else (expval-extractor-error 'pair v)))))

(define expval-car
  (lambda (v)
    (cases expval v
           (pair-val (car cdr) car)
           (else (expval-extractor-error 'car v)))))

(define expval-cdr
  (lambda (v)
    (cases expval v
           (pair-val (car cdr) cdr)
           (else (expval-extractor-error 'cdr v)))))

(define expval-null?
  (lambda (v)
    (cases expval v
           (empty-list-val () (bool-val #t))
           (else (bool-val #f)))))

(define list-val
  (lambda (args)
    (if (null? args) (empty-list-val)
      (pair-val (car args) (list-val (cdr args))))))

(define apply-elem
  (lambda (env)
    (lambda (elem)
      (value-of elem env))))

(define cond-val
  (lambda (conds acts env)
    (cond
      ((null? conds) (error 'cond-val "No conditions got into"))
      ((expval->bool (value-of (car conds) env)) (value-of (car acts) env))
      (else (cond-val (cdr conds) (cdr acts) env)))))

(define expval-extractor-error
  (lambda (variant value)
    (error 'expval-extractors "Looking for a ~s, found ~s"
                variant value)))


;;;;;;;;;;;;;;;; the interpreter ;;;;;;;;;;;;;;;;

;; value-of-program : Program -> ExpVal
;; Page: 71
(define value-of-program
  (lambda (pgm)
    (cases program pgm
	   (a-program (exp1)
		      (value-of exp1 (init-env))))))

;; value-of : Exp * Env -> ExpVal
;; Page: 71
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

       (add-exp (exp1 exp2)
                (let ((val1 (value-of exp1 env))
                      (val2 (value-of exp2 env)))
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val2)))
                (num-val (+ num1 num2)))))

       (mult-exp (exp1 exp2)
                (let ((val1 (value-of exp1 env))
                      (val2 (value-of exp2 env)))
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val2)))
                (num-val (* num1 num2)))))

       (div-exp (exp1 exp2)
                (let ((val1 (value-of exp1 env))
                      (val2 (value-of exp2 env)))
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val2)))
                (num-val (/ num1 num2)))))
	   
       (equal-exp (exp1 exp2)
                (let ((val1 (value-of exp1 env))
                      (val2 (value-of exp2 env)))
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val2)))
                (bool-val (= num1 num2)))))
       
       (greater-exp (exp1 exp2)
                (let ((val1 (value-of exp1 env))
                      (val2 (value-of exp2 env)))
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val2)))
                (bool-val (> num1 num2)))))

       (less-exp (exp1 exp2)
                (let ((val1 (value-of exp1 env))
                      (val2 (value-of exp2 env)))
                  (let ((num1 (expval->num val1))
                        (num2 (expval->num val2)))
                (bool-val (< num1 num2)))))

       (zero?-exp (exp1)
		      (let ((val1 (value-of exp1 env)))
			(let ((num1 (expval->num val1)))
			  (if (zero? num1)
			      (bool-val #t)
			      (bool-val #f)))))

       (empty-list-exp () (empty-list-val))
       (null?-exp (exp1)
            (expval-null? (value-of exp1 env)))

       (cons-exp (exp1 exp2)
            (let ((val1 (value-of exp1 env))
                  (val2 (value-of exp2 env)))
              (pair-val val1 val2)))

       (car-exp (exp1)
            (expval-car (value-of exp1 env)))

       (cdr-exp (exp1)
            (expval-cdr (value-of exp1 env)))

       (list-exp (args)
            (list-val (map (apply-elem env) args)))

       (cond-exp (conds acts)
            (cond-val conds acts env))

	   (if-exp (exp1 exp2 exp3)
		   (let ((val1 (value-of exp1 env)))
		     (if (expval->bool val1)
			 (value-of exp2 env)
			 (value-of exp3 env))))
	   (minus-exp (body-exp)
		      (let ((val1 (value-of body-exp env)))
			(let ((num (expval->num val1)))
			  (num-val (- 0 num)))))
	   (let-exp (var exp1 body)
		    (let ((val1 (value-of exp1 env)))
		      (value-of body
				(extend-env var val1 env))))
	   )))


;;
(define run
  (lambda (string)
    (value-of-program (scan&parse string))))



(run  "if zero?(-(11,11)) then 3 else 4")
;(num-val 3)

(run "minus(4)")
;(num-val -4)

(run  "if zero?(-(11,11)) then minus(3) else minus(4)")

(run "+(1,2)")
;(num-val 3)
(run "+(+(1,2), 3)")
;(num-val 6)
(run "*(2,3)")
;(num-val 6)
(run "/(1,2)")
;(num-val 0.5)

(run "equal?(1, 1)")
;(bool-val #t)
(run "greater?(1,2)")
;(bool-val #f)
(run "less?(1,2)")
;(bool-val $t)

(run "cons(1,2)")
;(pair-val (num-val 1) (num-val 2))
(run "car(cons(1,2))")
;(num-val 1)
(run "cdr(cons(1,2))")
;(num-val 2)
(run "null?(empty-list)")
;(bool-val #t)
(run "null?(cons(1,2))")
;(bool-val #f)

(run "list(1,2,3)")

(run "cond less?(1, 2) ==> 2 end") 
;(num-val 2)

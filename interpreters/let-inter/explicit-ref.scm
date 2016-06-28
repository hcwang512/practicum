(load-relative "./libs/init.scm")

;;;;;;;;;;;;;;;; expressed values ;;;;;;;;;;;;;;;;
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
    (expression
     ("-" "(" expression "," expression ")")
     diff-exp)

    (expression
     ("zero?" "(" expression ")")
     zero?-exp)

    (expression
     ("if" expression "then" expression "else" expression)
     if-exp)

    (expression (identifier) var-exp)

    (expression
     ("let" identifier "=" expression "in" expression)
     let-exp)

    (expression
     ("proc" "(" identifier ")" expression)
     proc-exp)

    (expression
     ("(" expression expression ")")
     call-exp)

    (expression
     ("letrec"
      (arbno identifier "(" identifier ")" "=" expression)
      "in" expression)
     letrec-exp)

    (expression
     ("newref" "(" expression ")")
     newref-exp)

    (expression
     ("deref" "(" expression ")")
     deref-exp)

    (expression
     ("setref" "(" expression "," expression ")")
     setref-exp)

    ))

  ;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;

(sllgen:make-define-datatypes the-lexical-spec the-grammar)

(define show-the-datatypes
  (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))

(define scan&parse
  (sllgen:make-string-parser the-lexical-spec the-grammar))


;;; an expressed value is either a number, a boolean, a procval, or a
;;; reference.
(define-datatype expval expval?
  (num-val
   (value number?))
  (bool-val
   (boolean boolean?))
  (proc-val
   (proc proc?))
  (ref-val
   (ref reference?))
  )

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

(define expval->ref
  (lambda (v)
    (cases expval v
	   (ref-val (ref) ref)
	   (else (expval-extractor-error 'reference v)))))

(define expval-extractor-error
  (lambda (variant value)
    (error 'expval-extractors "Looking for a ~s, found ~s"
		variant value)))

;;;;;;;;;;;;;;;; procedures ;;;;;;;;;;;;;;;;

(define-datatype proc proc?
  (procedure
   (bvar symbol?)
   (body expression?)
   (env environment?)))

(define-datatype environment environment?
  (empty-env)
  (extend-env
   (bvar symbol?)
   (bval expval?)
   (saved-env environment?))
  (extend-env-rec*
   (proc-names (list-of symbol?))
   (b-vars (list-of symbol?))
   (proc-bodies (list-of expression?))
   (saved-env environment?)))

(define init-env
  (lambda ()
    (empty-env)))

;;;;;;;;;;;;;;;; environment constructors and observers ;;;;;;;;;;;;;;;;
(define apply-env
  (lambda (env search-sym)
    (cases environment env
           (empty-env ()
                      (error 'apply-env "No binding for ~s" search-sym))
           (extend-env (bvar bval saved-env)
                       (if (eqv? search-sym bvar)
                           bval
                           (apply-env saved-env search-sym)))
           (extend-env-rec* (p-names b-vars p-bodies saved-env)
                            (cond
                             ((location search-sym p-names)
                              => (lambda (n)
                                   (proc-val
                                    (procedure
                                     (list-ref b-vars n)
                                     (list-ref p-bodies n)
                                     env))))
                             (else (apply-env saved-env search-sym)))))))

(define location
  (lambda (sym syms)
    (cond
     ((null? syms) #f)
     ((eqv? sym (car syms)) 0)
     ((location sym (cdr syms))
      => (lambda (n)
           (+ n 1)))
     (else #f))))


;; env->list : Env -> List
;; used for pretty-printing and debugging
(define env->list
  (lambda (env)
    (cases environment env
	   (empty-env () '())
	   (extend-env (sym val saved-env)
		       (cons
			(list sym (expval->printable val))
			(env->list saved-env)))
	   (extend-env-rec* (p-names b-vars p-bodies saved-env)
			    (cons
			     (list 'letrec p-names '...)
			     (env->list saved-env))))))

;; expval->printable : ExpVal -> List
;; up with env->list
(define expval->printable
  (lambda (val)
    (cases expval val
	   (proc-val (p)
		     (cases proc p
			    (procedure (var body saved-env)
				       (list 'procedure var '... (env->list saved-env)))))
	   (else val))))



(define instrument-let (make-parameter #f))

;; value-of-program : Program -> ExpVal
;; Page: 110
(define value-of-program
  (lambda (pgm)
    (initialize-store!)               ; new for explicit refs.
    (cases program pgm
	   (a-program (exp1)
		      (value-of exp1 (init-env))))))

;; value-of : Exp * Env -> ExpVal
;; Page: 113
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

	   (proc-exp (var body)
		     (proc-val (procedure var body env)))

	   (call-exp (rator rand)
		     (let ((proc (expval->proc (value-of rator env)))
			   (arg (value-of rand env)))
		       (apply-procedure proc arg)))

	   (letrec-exp (p-names b-vars p-bodies letrec-body)
		       (value-of letrec-body
				 (extend-env-rec* p-names b-vars p-bodies env)))

	   (newref-exp (exp1)
		       (let ((v1 (value-of exp1 env)))
			 (ref-val (newref v1))))

	   (deref-exp (exp1)
		      (let ((v1 (value-of exp1 env)))
			(let ((ref1 (expval->ref v1)))
			  (deref ref1))))

	   (setref-exp (exp1 exp2)
	   	       (let ((ref1 (expval->ref (value-of exp1 env)))
	   		     (v2 (value-of exp2 env)))
	   		 (begin
	   		   (setref! ref1 v2)
	   		   (num-val 1))))
	   )))

;;
;; instrumented version
(define apply-procedure
  (lambda (proc1 arg)
    (cases proc proc1
	   (procedure (var body saved-env)
		      (let ((r arg))
			(let ((new-env (extend-env var r saved-env)))
			  (if (instrument-let)
			      (begin
				(printf
				 "entering body of proc ~s with env =~%"
				 var)
				(pretty-print (env->list new-env))
				(printf "store =~%")
				(pretty-print (store->readable (get-store-as-list)))
				(printf "~%")))
			  (value-of body new-env)))))))


;; store->readable : Listof(List(Ref,Expval))
(define store->readable
  (lambda (l)
    (map
     (lambda (p)
       (cons
	(car p)
	(expval->printable (cadr p))))
     l)))


(define run
  (lambda (string)
    (value-of-program (scan&parse string))))

;;;;;;;;;;;;;;;; references and the store ;;;;;;;;;;;;;;;;
  
  ;;; world's dumbest model of the store:  the store is a list and a
  ;;; reference is number which denotes a position in the list.

  ;; the-store: a Scheme variable containing the current state of the
  ;; store.  Initially set to a dummy variable.

(define the-store 'uninitialized)
;; empty-store : () -> Sto
;;   ;; Page: 111
(define empty-store
  (lambda () '()))

 ;; initialize-store! : () -> Sto
 ;; usage: (initialize-store!) sets the-store to the empty-store
 ;; Page 111
(define initialize-store!
  (lambda () set! the-store (empty-store)))

;; get-store : () -> Sto
;;   ;; Page: 111
;;     ;; This is obsolete.  Replaced by get-store-as-list below
(define get-store
  (lambda () the-store))

;; reference? : SchemeVal -> Bool
;;   ;; Page: 111
(define reference?
  (lambda (v)
    (integer? v)))

;; newref : ExpVal -> Ref
;;   ;; Page: 111
(define newref
  (lambda (val)
    (let ((next-ref (length the-store)))
      (set! the-store (append the-store (list val)))
      (when (instrument-newref) (error "newref: allocating location ~s with initial contents"))
      next-ref)))

 ;; deref : Ref -> ExpVal
 ;;   ;; Page 111
 (define deref 
   (lambda (ref)
     (list-ref the-store ref)))

;; setref! : Ref * ExpVal -> Unspecified
;;
(define setref!
  (lambda (ref val)
    (set! the-store
      (letrec
        ((setref-inner
            ;; returns a list like store1, except that position ref1
            ;; ;; contains val
          (lambda (store1 ref1)
            (cond
               ((null? store1) (error "invalid reference"))
               ((zero? ref1)
                (cons val (cdr store1)))
               (else
                 (cons
                   (car store1)
                   (setref-inner
                     (cdr store1) (- ref1 1))))))))
        (setref-inner the-store ref)))))

;; get-store-as-list : () -> Listof(List(Ref,Expval))
  ;; Exports the current state of the store as a scheme list.
  ;; (get-store-as-list '(foo bar baz)) = ((0 foo)(1 bar) (2 baz))
  ;;   where foo, bar, and baz are expvals.
  ;; If the store were represented in a different way, this would be
  ;; replaced by something cleverer.
  ;; Replaces get-store (p. 111)
(define get-store-as-list
 (lambda ()
   (letrec
     ((inner-loop
        ;; convert sto to list as if its car was location n
        (lambda (sto n)
          (if (null? sto)
            '()
            (cons
              (list n (car sto))
              (inner-loop (cdr sto) (+ n 1)))))))
     (inner-loop the-store 0))))

)

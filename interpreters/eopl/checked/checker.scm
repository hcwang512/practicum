(module checker (lib "eopl.ss" "eopl")

  (require "drscheme-init.scm")
  (require "lang.scm")

  (provide type-of type-of-program)

  ;; check-equal-type! : Type * Type * Exp -> Unspecified
  ;; Page: 242
  (define check-equal-type!
    (lambda (ty1 ty2 exp)
      (when (not (equal? ty1 ty2))
        (report-unequal-types ty1 ty2 exp))))

  (define check-equal-type*!
    (lambda (ty1s ty2s exps)
      (when (not (null? ty1s))
        (begin
          (check-equal-type! (car ty1s) (car ty2s) (car exps))
          (check-equal-type*! (cdr ty1s) (cdr ty2s) (cdr exps))))))

  ;; report-unequal-types : Type * Type * Exp -> Unspecified
  ;; Page: 243
  (define report-unequal-types
    (lambda (ty1 ty2 exp)
      (eopl:error 'check-equal-type!  
          "Types didn't match: ~s != ~a in~%~a"
          (type-to-external-form ty1)
          (type-to-external-form ty2)
          exp)))

  ;;;;;;;;;;;;;;;; The Type Checker ;;;;;;;;;;;;;;;;
  
  ;; type-of-program : Program -> Type
  ;; Page: 244
  (define type-of-program
    (lambda (pgm)
      (cases program pgm
        (a-program (exp1) (type-of exp1 (init-tenv))))))

  ;; type-of : Exp * Tenv -> Type
  ;; Page 244--246
  (define type-of
    (lambda (exp tenv)
      (cases expression exp

        ;; \commentbox{\hastype{\tenv}{\mv{num}}{\mathtt{int}}}
        (const-exp (num) (int-type))

        ;; \commentbox{\hastype{\tenv}{\var{}}{\tenv{}(\var{})}}
        (var-exp (var) (apply-tenv tenv var))

        ;; \commentbox{\diffrule}
        (diff-exp (exp1 exp2)
          (let ((ty1 (type-of exp1 tenv))
                (ty2 (type-of exp2 tenv)))
            (check-equal-type! ty1 (int-type) exp1)
            (check-equal-type! ty2 (int-type) exp2)
            (int-type)))

        ;; \commentbox{\zerorule}
        (zero?-exp (exp1)
          (let ((ty1 (type-of exp1 tenv)))
            (check-equal-type! ty1 (int-type) exp1)
            (bool-type)))

        ;; \commentbox{\condrule}
        (if-exp (exp1 exp2 exp3)
          (let ((ty1 (type-of exp1 tenv))
                (ty2 (type-of exp2 tenv))
                (ty3 (type-of exp3 tenv)))
            (check-equal-type! ty1 (bool-type) exp1)
            (check-equal-type! ty2 ty3 exp)
            ty2))

        ;; \commentbox{\letrule}
        (let-exp (vars exps body)
          (let ((exps-type (map (lambda (ele) (type-of ele tenv)) exps)))
            (type-of body
              (extend-tenv* vars exps-type tenv))))

        ;; \commentbox{\procrulechurch}
        (proc-exp (vars var-types body)
          (let ((result-type
                  (type-of body
                    (extend-tenv* vars var-types tenv))))
            (proc-type var-types result-type)))

        (set-exp (var exp1)
          (type-of exp1 tenv))

        ;; \commentbox{\apprule}
        (call-exp (rator rands) 
          (let ((rator-type (type-of rator tenv))
                (rand-types  (map (lambda (ele) (type-of ele tenv)) rands)))
            (cases type rator-type
              (proc-type (arg-types result-type)
                (begin
                  (check-equal-type! arg-types rand-types rands)
                  result-type))
              (else
                (report-rator-not-a-proc-type rator-type rator)))))

        ;; \commentbox{\letrecrule}
        (letrec-exp (p-result-types p-names b-varss b-var-typess p-bodys
                      letrec-body)
          (let ((tenv-for-letrec-body
                  (extend-tenv-rec p-names
                    b-varss b-var-typess p-bodys p-result-types
                    tenv)))
            (let ((p-body-types 
                    (map (lambda (i) (type-of (list-ref p-bodys i)
                      (extend-tenv* (list-ref b-varss i) (list-ref b-var-typess i)
                        tenv-for-letrec-body))) (range (length p-bodys)))))
              (check-equal-type*!
                p-body-types p-result-types p-bodys)
              (type-of letrec-body tenv-for-letrec-body)))))))
    
  (define range
    (lambda (n)
      (define (helper count acc)
        (if (<= count n) acc
          (helper (+ 1 count) (cons count acc))))
      (helper 0 '())))

  (define report-rator-not-a-proc-type
    (lambda (rator-type rator)
      (eopl:error 'type-of-expression
        "Rator not a proc type:~%~s~%had rator type ~s"   
           rator 
           (type-to-external-form rator-type))))

  ;;;;;;;;;;;;;;;; type environments ;;;;;;;;;;;;;;;;
    
  (define-datatype type-environment type-environment?
    (empty-tenv-record)
    (extended-tenv-record
      (sym symbol?)
      (type type?)
      (tenv type-environment?))
    (extended-tenv-record-rec
      (p-names (list-of symbol?))
      (b-varss (list-of (list-of symbol?)))
      (b-typess (list-of (list-of type?)))
      (proc-bodys (list-of expression?))
      (p-result-types (list-of type?))
      (tenv type-environment?)))
    
  (define empty-tenv empty-tenv-record)
  (define extend-tenv extended-tenv-record)
  (define extend-tenv-rec extended-tenv-record-rec)
  (define extend-tenv*
    (lambda (vars types tenv)
      (if (null? vars) tenv
        (extend-tenv* (cdr vars) (cdr types) (extend-tenv (car vars) (car types) tenv)))))
    
  (define apply-tenv 
    (lambda (tenv sym)
      (cases type-environment tenv
        (empty-tenv-record ()
          (eopl:error 'apply-tenv "Unbound variable ~s" sym))
        (extended-tenv-record (sym1 val1 old-env)
          (if (eqv? sym sym1) 
            val1
            (apply-tenv old-env sym)))
        (extended-tenv-record-rec (p-names b-varss b-typess p-bodys p-result-types old-env)
          (letrec ((search (lambda (proc-names proc-types var-typess)
                          (cond
                            ((null? proc-names) (apply-tenv old-env sym))
                            ((eqv? sym (car proc-names)) (proc-type (car var-typess) (car proc-types)))
                            (else (search (cdr proc-names) (cdr proc-types) (cdr var-typess)))))))
            (search p-names p-result-types b-typess))))))

  (define find-in-lists 
    (lambda (varss typess sym)
      (cond
        ((null? varss) #f)
        ((null? (car varss)) (find-in-lists (cdr varss) (cdr typess) sym))
        ((eqv? (caar varss) sym) (caar typess))
        (else (find-in-lists (cons (cdar varss) (cdr varss)) (cons (cdar typess) (cdr typess)) sym)))))

  (define init-tenv
    (lambda ()
      (extend-tenv 'x (int-type) 
        (extend-tenv 'v (int-type)
          (extend-tenv 'i (int-type)
            (empty-tenv))))))

  )

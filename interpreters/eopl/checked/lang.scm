(module lang (lib "eopl.ss" "eopl") 

  ;; grammar for the CHECKED language
  
  (require "drscheme-init.scm")
  
  (provide (all-defined-out))

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
       ("let" (arbno identifier "=" expression) "in" expression)
       let-exp)   

      (expression
       ("proc" "(" (arbno identifier ":" type) ")" expression)
       proc-exp)

      (expression
        ("set" identifier "=" expression)
        set-exp)
      (expression
       ("(" expression (arbno expression) ")")
       call-exp)

      (expression
        ("letrec"
          (arbno type identifier "(" (arbno identifier ":" type) ")" "=" expression)
           "in" expression)
        letrec-exp)

      (type
       ("int")
       int-type)
      
      (type
       ("bool")
       bool-type)
      
      (type
       ("(" (arbno type) "->" type ")")
       proc-type)
      
      ))

  ;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;
  
  (sllgen:make-define-datatypes the-lexical-spec the-grammar)
  
  (define show-the-datatypes
    (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))
  
  (define scan&parse
    (sllgen:make-string-parser the-lexical-spec the-grammar))
  
  (define just-scan
    (sllgen:make-string-scanner the-lexical-spec the-grammar))
  
;;;;;;;;;;;;;;;; type-to-external-form ;;;;;;;;;;;;;;;;

  ;; type-to-external-form : Type -> List
  ;; Page: 243
  (define type-to-external-form
    (lambda (ty)
      (cases type ty
        (int-type () 'int)
        (bool-type () 'bool)
        (proc-type (arg-types result-type)
          (list
            (map (lambda (ele) (type-to-external-form ele)) arg-types)
            '->
            (type-to-external-form result-type))))))

  )

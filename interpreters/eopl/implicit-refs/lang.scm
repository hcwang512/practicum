(module lang (lib "eopl.ss" "eopl")                
  
  ;; language for IMPLICIT-REFS

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
    '((program (statement) a-program)

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
        ("letmutable" (arbno identifier "=" expression ) "in" expression)
        letmutable-exp)
      (expression
       ("proc" "(" (arbno identifier) ")" expression)
       proc-exp)

      (expression
       ("(" expression (arbno expression) ")")
       call-exp)

      (expression
        ("letrec"
          (arbno identifier "(" (arbno identifier) ")" "=" expression)
           "in" expression)
        letrec-exp)
      
      (expression
        ("begin" expression (arbno ";" expression) "end")
        begin-exp)

      (expression
        ("setdynamic" identifier "=" expression "during" expression)
        setdynamic-exp)
      ;; new for implicit-refs

      (expression
        ("set" identifier "=" expression)
        assign-exp)

      (statement
        (identifier "=" expression)
        assign-stat)
      (statement
        ("print" expression) print-stat)
      (statement
        ("{" (separated-list statement ";") "}") block-stat)
      (statement
        ("if" expression statement statement)
        if-stat)
      (statement
        ("while" expression statement)
        while-stat)
      (statement
        ("var" (separated-list identifier ",") ";" statement)
        declare-stat)
         ))

  ;;;;;;;;;;;;;;;; sllgen boilerplate ;;;;;;;;;;;;;;;;
  
  (sllgen:make-define-datatypes the-lexical-spec the-grammar)
  
  (define show-the-datatypes
    (lambda () (sllgen:list-define-datatypes the-lexical-spec the-grammar)))
  
  (define scan&parse
    (sllgen:make-string-parser the-lexical-spec the-grammar))
  
  (define just-scan
    (sllgen:make-string-scanner the-lexical-spec the-grammar))
  
  )

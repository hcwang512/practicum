(define (Y* . l)
 ((lambda (u) (u u))
    (lambda (p)
       (map (lambda (li) (lambda x (apply (apply li (p p)) x))) l))))

(define ev-od (Y*  (lambda (ev? od?) (lambda (x) (or (zero? x) (od? (- x 1)))))
                   (lambda (ev? od?) (lambda (x) (and (not (zero? x)) (ev? (- x 1)))))))

(define ev? (list-ref ev-od 0))
(define od? (list-ref ev-od 1))

;(ev? 10)
;#t
;(od? 10)
;#f
;
;
;ref:
;http://okmij.org/ftp/Computation/fixed-point-combinators.html#Poly-variadic

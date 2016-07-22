;(require racket/trace)

(define remove/k
  (lambda (n lst cont)
    (cond
      ((null? lst) (cont '()))
      ((eq? n (car lst))
       ;(print "~s   ~s" lst (cont 10))
       (remove/k n (cdr lst) cont ))
      ((number? (car lst)) (remove/k n (cdr lst) (lambda (val) (cont (cons (car lst) val)))))
      (else (remove/k n (car lst) (lambda (val1) (remove/k n (cdr lst) (lambda (val2) (cont (cons val1 val2))))))))))

(define remove/t
  (lambda (n lst)
    (remove/k n lst (lambda (val) val))))

(define (test name a b)
  (if (equal? a b) (printf "~s right ~%" name)
    (printf "opps! ~s wrong  ~s   ... ~s ~%" name b a)))

(test "remove/t-1" (remove/t 1 '(1)) '())
(test "remove/t-2" (remove/t 2 '(1 2 3)) '(1 3))
(test "remove/t-3" (remove/t 10 '(1 2 3 4 5)) '(1 2 3 4 5))
(test "remove/t-4" (remove/t 1 '((1) (1 2) (2 3))) '(() (2) (2 3)))

(define occurs-in/k
  (lambda (n lst cont)
    (cond
      ((null? lst) (cont #f))
      ((eq? n (car lst)) (cont #t))
      ((number? (car lst)) (occurs-in/k n (cdr lst) cont))
      (else (occurs-in/k n (car lst) (lambda (val1) (occurs-in/k n (cdr lst) (lambda (val2) (cont (or val1 val2))))))))))

(define occurs-in
  (lambda (n lst)
    (occurs-in/k n lst (lambda (val) val))))

(test "occurs-in-1" (occurs-in 1 '(1 2 3)) #t)
(test "occurs-in-2" (occurs-in 1 '(3 2 1)) #t)
(test "occurs-in-3" (occurs-in 4 '(1 2 3)) #f)
(test "occurs-in-4" (occurs-in 1 '((2 3) (3 4) (2 1))) #t)

(define depth
  (lambda (lst)
    (depth/k lst (lambda (val) val))))

(define depth/k
  (lambda (lst cont)
    (cond
      ((null? lst) (cont 1))
      ((list? (car lst))
       (depth/k (car lst) (lambda (val1) (depth/k (cdr lst) (lambda (val2) (cont (max (+ val1 1) val2)))))))
      (else (depth/k (cdr lst) (lambda (val) (cont val)))))))

(test "depth-1" (depth '()) 1)
(test "depth-2" (depth '(1 2 3 4 5)) 1)
(test "depth-3" (depth '((1 (1 2) ()) (2 3) (2 4 (3 4)))) 3)

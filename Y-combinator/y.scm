(define Y1 (lambda (f)
  (let ((h (lambda (g) (lambda (x) ((f (g g)) x)))))
    (h h))))

(define Y2 (lambda (f)
  ((lambda (g) (lambda (x) ((f (g g)) x)))
   (lambda (g) (lambda (x) ((f (g g)) x))))))

(define Y3 (lambda (f)
  ((lambda (t) (t t))
   (lambda (g) (lambda (x) ((f (g g)) x))))))

(define fac
  (lambda (f)
    (lambda (n)
      (if (= 0 n) 1 (* n (f (- n 1)))))))

(define fact (Y1 fac))

;(fact 10)
;3628800

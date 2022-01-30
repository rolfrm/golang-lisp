(define t (= 1 1))
(define list (lambda (&rest lst) lst))
(define not (lambda (x) (= x nil)))
(define append2 
    (lambda (lst) 
        (if (not (cdr lst))
            (car lst) 
            (cons (car lst) (append2 (cdr lst))))))

(define append 
    (lambda (&rest lst) 
        (append2 lst)))

(define defun (macro (lambda (name args &rest body) (list (quote define) name (append (quote lambda) args body)))))
(define defmacro (macro (lambda (name args &rest body) (list (quote define) name (list (quote macro) (append (quote lambda) args body))))))
	
(defmacro when (test &rest body)
    (list (quote if) test (append (quote progn) body))
)

(defmacro unless (test &rest body)
    (append (quote when) (list (quote not) test) body)
)

(defun print-hello-world () 
    (print "hello") 
    (print "world"))

(print "Hello World")
(print (+ 1 2 3 2.5))
(print (type-of "hello World"))

"
(defun map (f lst) 
    (when lst
        (f (car lst))
        (map f (cdr lst)))
 )
 "
(print (not nil))
(print (append 1 2 3 (list 4 5)))
(when t 
    (print-hello-world))
(unless nil (print-hello-world))
(defun do-times (n f2)
    (let ((x 0)) ;; hej hej
    (let ((f (lambda ()
        (set x (+ 1 x))
        (f2)
        (when (< x n) (f))    
    )))
    (f))
)
)

;; now print hello world five times.
(do-times 5 print-hello-world)

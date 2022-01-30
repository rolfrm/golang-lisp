
(define list (lambda (&rest lst) lst))
(define append2 
    (lambda (lst) 
        (if (cdr lst)
            lst 
            (cons (car lst) (append2 (cdr lst))))))
(define append 
    (lambda (&rest lst) 
        (append2 lst)))


(define defun (macro (lambda (name args &rest body) (list (quote define) name (list (quote lambda) args (car body))))))
(define defmacro (macro (lambda (name args &rest body) (list (quote define) name (list (quote macro) (list (quote lambda) args (car body)))))))
	
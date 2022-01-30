package golisp

import (
	"log"
	"testing"
)

func TestPrinttest(t *testing.T) {
	lisp := NewLispContext()
	lisp.EvalString("    1123  (+ 1 2) \"3 4 5 \" (+ 2 3 (* 4 5))")
	lisp.EvalString("(let ((a 4) (b 5)) (+ a b))")
	lisp.EvalString("((lambda (x) (* 2 x)) 4)")
	lisp.EvalString("((let ((y 7)) (lambda (x) (* y x))) 5)")
	lisp.EvalString("(let ((x 2)) (set x 3) x)")
	lisp.EvalString("(define test 3)")
	lisp.EvalString("test")
	r := lisp.EvalString("(car (cons 1 2))")
	r2 := lisp.EvalString("(cdr (cons 1 2))")
	log.Println(r, r2)
	lisp.EvalString("(print \"Hello world\")")
	lisp.EvalString("(define testf (lambda () 55))")
	lisp.EvalString("(print (testf))")
	lisp.EvalString("(print (if 5 5 3))")
	lisp.EvalString("(print (if nil 5 3))")
	lisp.EvalString("(define fib ())")
	lisp.EvalString("(print fib)")
	lisp.EvalString("(set fib (lambda (x) (if (< x 2) x (+ (fib (- x 1)) (fib (- x 2))))))")
	lisp.EvalString("(print (fib 15))")
	lisp.EvalString("(print (quote quoted 1 2))")
	lisp.EvalString("(define list (lambda (&rest lst) lst))")
	lisp.EvalString("(print (cdr (list 1 2 3 4)))")
	lisp.EvalString("(define one (macro (lambda (&rest x) 1)))")
	lisp.EvalString("(define two (macro (lambda (&rest x) (car (cdr x)))))")
	lisp.EvalString("(print (one 5 3 4))")
	lisp.EvalString("(print (two 5 3 4))")
	lisp.EvalString("(define three (macro (lambda (name items &rest x) (print (list (quote print) 4)))))")
	lisp.EvalString("(print (three a (b c) d))")
	lisp.EvalString("(define defun (macro (lambda (name args &rest body) (list (quote define) name (list (quote lambda) args (car body))))))")
	lisp.EvalString("(define defmacro (macro (lambda (name args &rest body) (list (quote define) name (list (quote macro) (list (quote lambda) args (car body)))))))")
	lisp.EvalString("(defun add (a b) (+ a b))")
	lisp.EvalString("(print (add 3 4))")
	//lisp.EvalString("(error \"Oh no\")")
	//lisp.EvalString("(define m1 (macro (x) x)))")
	//lisp.EvalString("(m1 3)")
}

func TestLoadFromFiletest(t *testing.T) {
	lisp := NewLispContext()
	lisp.EvalFile("lisp1.lisp")
}

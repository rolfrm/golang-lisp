package main

import (
	"golisp_repl/golisp"
	"log"
	"os"
)

func main() {
	lisp := golisp.NewLispContext()
	for _, x := range os.Args[1:] {
		log.Println("file: ", x)
		lisp.EvalFile(x)
	}

}

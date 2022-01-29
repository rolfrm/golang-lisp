package golisp

import (
	"bufio"
	"bytes"
	"fmt"
	"log"
	"strconv"
	"strings"
	"unicode"
)

type LispValue interface{}

type Cons struct {
	Car LispValue
	Cdr LispValue
}

func cons(a, b LispValue) *Cons {
	return &Cons{Car: a, Cdr: b}
}

func (c *Cons) String() string {
	var sb strings.Builder
	sb.WriteString("(")
	for {
		sb.WriteString(fmt.Sprint(c.Car))
		if c.Cdr == nil {
			sb.WriteString(")")
			break
		}
		n, ok := c.Cdr.(*Cons)
		if ok {
			sb.WriteString(" ")
			c = n
			continue
		} else {
			sb.WriteString(" . ")
			sb.WriteString(fmt.Sprint(c.Cdr))
			sb.WriteString(")")
			break
		}

	}
	return sb.String()
}

func car(a LispValue) LispValue {
	v, e := a.(*Cons)
	if e {
		return v.Car
	}
	return nil
}
func cdr(a LispValue) LispValue {
	v, e := a.(*Cons)
	if e {
		return v.Cdr
	}
	return nil
}
func caddr(a LispValue) LispValue {
	return car(cddr(a))
}
func cadr(a LispValue) LispValue {
	return car(cdr(a))
}
func cddr(a LispValue) LispValue {
	return cdr(cdr(a))
}

//func setf(place LispValue, value LispValue) LispValue {

//}

type LispScope struct {
	UpScope *LispScope
	Scope   map[*Symbol]LispValue
}

func NewLispScope() LispScope {
	return LispScope{Scope: make(map[*Symbol]LispValue)}
}

func (s *LispScope) SubScope() *LispScope {
	return &LispScope{UpScope: s, Scope: make(map[*Symbol]LispValue)}
}

func (s *LispScope) GetValue(sym *Symbol) LispValue {
	v, ok := s.Scope[sym]
	if ok {
		return v
	}
	if s.UpScope == nil {
		return nil
	}
	return s.UpScope.GetValue(sym)
}

func (s *LispScope) OverwriteValue(sym *Symbol, val LispValue) {
	s.Scope[sym] = val
}

func (s *LispScope) TopScope() *LispScope {
	if s.UpScope == nil {
		return s
	}
	return s.UpScope.TopScope()
}

func (s *LispScope) SetValue(sym *Symbol, val LispValue) LispValue {
	v, ok := s.Scope[sym]
	if ok {
		s.Scope[sym] = val
		return v
	}
	if s.UpScope == nil {
		return nil
	}
	return s.UpScope.SetValue(sym, val)
}

type LispContext struct {
	Symbols SymbolTable
	Globals LispScope
}

func (l *LispContext) GetSymbol(key string) *Symbol {
	s := l.Symbols.Get(key)
	return s
}

func (l *LispContext) GetOrCreateSymbol(key string) *Symbol {
	return l.Symbols.GetOrCreate(key)
}

func (l *LispContext) SubContext() {

}

func NewLispContext() LispContext {
	v := LispContext{
		Globals: NewLispScope(),
		Symbols: SymbolTable{
			Symbols: make(map[string]*WeakRef)}}
	return v
}

type TokenType string

const (
	None        TokenType = "None"
	StringToken           = "String"
	SymbolToken           = "Symbol"
	ListToken             = "List"
)

type Token struct {
	Type      TokenType
	SubTokens []Token
	Data      string
}

type ParserContext struct {
	writeBuffer WriteBuffer
}

func (l *LispContext) EvalString(str string) {
	log.Printf("Parsing %v", str)
	rd := strings.NewReader(str)
	l.EvalStream(bufio.NewReader(rd))
}

func (lisp *LispContext) ReadToken(token Token) LispValue {
	switch token.Type {
	case None:
		return nil
	case StringToken:
		return string(token.Data)
	case ListToken:
		var c []*Cons = make([]*Cons, len(token.SubTokens))

		for i, x := range token.SubTokens {
			c[i] = cons(lisp.ReadToken(x), nil)
		}
		for i := 1; i < len(token.SubTokens); i += 1 {
			i2 := len(token.SubTokens) - i - 1
			c[i2].Cdr = c[i2+1]
		}
		if len(c) == 0 {
			return nil
		}
		return c[0]
	case SymbolToken:
		i, err := strconv.ParseInt(token.Data, 10, 64)
		if err == nil {
			return i
		}
		f, err := strconv.ParseFloat(token.Data, 64)
		if err == nil {
			return f
		}
		return lisp.Symbols.GetOrCreate(token.Data)
	}
	log.Fatal("Unexpected")
	return nil
}

type Builtin struct {
	Invoke func(vars LispValue) LispValue
}

type Lambda *Cons

func (lisp *LispContext) EvalStream(r *bufio.Reader) LispValue {
	ctx := ParserContext{}

	symPlus := lisp.Symbols.GetOrCreate("+")
	lisp.Globals.Scope[symPlus] = Builtin{Invoke: func(values LispValue) LispValue {
		log.Println(">>>>> ", values)
		var acc int64 = 0
		for i := values; i != nil; i = cdr(i) {
			x := car(i).(int64)
			acc = acc + x
		}
		return acc
	}}

	symSub := lisp.Symbols.GetOrCreate("-")
	lisp.Globals.Scope[symSub] = Builtin{Invoke: func(values LispValue) LispValue {
		var acc int64 = 0
		for i := values; i != nil; i = cdr(i) {

			x := car(i).(int64)
			if i == values {
				acc = x
			} else {
				acc = acc - x
			}
		}
		return acc
	}}

	symMul := lisp.Symbols.GetOrCreate("*")
	lisp.Globals.Scope[symMul] = Builtin{Invoke: func(values LispValue) LispValue {
		var acc int64 = 0
		for i := values; i != nil; i = cdr(i) {

			x := car(i).(int64)
			if i == values {
				acc = x
			} else {
				acc = acc * x
			}
		}
		return acc
	}}

	ctx.writeBuffer = bytes.NewBuffer(make([]byte, 1))
	for {
		t := TokenizeStream(ctx, r)
		log.Printf(";. %v", t)
		t2 := lisp.ReadToken(t)
		log.Printf(";. %v", t2)
		r := EvalLisp(&lisp.Globals, t2)

		log.Printf(">> %v", r)
		if t.Type == None {
			break
		}
	}
	return nil
}

func (l *LispScope) Let(argForm LispValue) *LispScope {
	ctx2 := l.SubScope()
	return ctx2
}

type LambdaFunction struct {
	scope *LispScope
	body  LispValue
	args  *Cons
}

func EvalLisp(scope *LispScope, v LispValue) LispValue {
	cns, ok := v.(*Cons)
	if !ok { // not a cons -> just return the value
		sym, ok := v.(*Symbol)
		if ok {
			return scope.GetValue(sym)
		}
		return v
	}

	fst := car(cns)
	sym, ok := fst.(*Symbol)
	if ok {
		if sym.Name == "lambda" {
			args, ok := cadr(cns).(*Cons)
			body, ok2 := cddr(cns).(*Cons)
			if !ok {
				log.Fatal("args")
			}
			if !ok2 {
				log.Fatal("body")
			}
			return LambdaFunction{args: args, body: body, scope: scope}
		}
		if sym.Name == "let" {
			argForm := cadr(cns)
			bodyForm := cddr(cns)
			scope2 := scope.Let(argForm)
			for i := argForm; i != nil; i = cdr(i) {
				nv := car(i).(*Cons)
				name := car(nv).(*Symbol)
				value := EvalLisp(scope2, cadr(nv))
				scope.OverwriteValue(name, value)
			}
			return EvalLisp(scope2, car(bodyForm))
		}
		if sym.Name == "set" || sym.Name == "define" {
			name := cadr(cns)
			value := caddr(cns)

			r := EvalLisp(scope, value)
			if sym.Name == "define" {
				scope.TopScope().OverwriteValue(name.(*Symbol), r)
			} else {
				scope.SetValue(name.(*Symbol), r)

			}
			return r
		}
	}

	var rest LispValue = cns
	args := []*Cons{}
	for j, i := 0, rest; i != nil; j, i = j+1, cdr(i) {
		arg := EvalLisp(scope, car(i))

		args = append(args, cons(arg, nil))
		if j > 0 {
			args[j-1].Cdr = args[j]
		}
	}

	fval := car(args[0])
	b, ok := fval.(Builtin)
	if ok {
		return b.Invoke(args[1])
	}
	l, ok := fval.(LambdaFunction)

	if ok {
		scope2 := l.scope.SubScope()
		var args2 LispValue = l.args
		for a, j := args2, cdr(args[0]).(LispValue); a != nil && j != nil; a, j = cdr(a), cdr(j) {
			t1, t2 := car(a).(*Symbol), car(j)
			scope2.OverwriteValue(t1, t2)
		}
		var result LispValue
		for bodyIt := l.body; bodyIt != nil; bodyIt = cdr(bodyIt) {
			EvalLisp(scope2, car(bodyIt))
		}
		return result
	}

	switch len(args) {
	case 0:
		f, ok := fval.(func() LispValue)
		if ok {
			return f()
		}
		break
	}

	log.Fatal("Cannot handle function", sym, fst)
	return nil
}

func TokenizeStream(ctx ParserContext, r *bufio.Reader) Token {
	skipWhiteSpace(ctx, r)
	rune, _, _ := r.ReadRune()
	if rune == '(' {
		lst := []Token{}
		for {

			tk := TokenizeStream(ctx, r)
			skipWhiteSpace(ctx, r)
			if tk.Type == None {
				break
			}
			lst = append(lst, tk)
		}

		r2, _, _ := r.ReadRune()
		if r2 != ')' {
			log.Fatalf("unexpected rune: %v", strconv.QuoteRune(r2))
		}
		return Token{Type: ListToken, SubTokens: lst}

	} else {
		r.UnreadRune()
		td := readTokenData(ctx, r)
		return td
	}
}

func readRunes(r *bufio.Reader, w WriteBuffer, f func(c rune) bool) {
	for {
		r2, _, e := r.ReadRune()
		if e != nil {
			break
		}
		if f(r2) {

			w.WriteRune(r2)
		} else {
			r.UnreadRune()
			break
		}
	}
}

func peekRune(r *bufio.Reader) rune {
	r2, _, _ := r.ReadRune()
	r.UnreadRune()
	return r2
}

func skipWhiteSpace(ctx ParserContext, r *bufio.Reader) {
	ctx.writeBuffer.Reset()
	readRunes(r, ctx.writeBuffer, func(x rune) bool { return unicode.IsSpace(x) })
}

func readString(ctx ParserContext, r *bufio.Reader) []byte {

	if peekRune(r) != '"' {
		return nil
	}
	r.ReadRune()
	ctx.writeBuffer.Reset()
	readRunes(r, ctx.writeBuffer, func(x rune) bool {
		if x == '\\' {
			r.ReadRune()
		} else if x == '"' {
			return false
		}
		return true
	})
	r.ReadRune()
	return ctx.writeBuffer.Bytes()
}

func readTokenData(ctx ParserContext, r *bufio.Reader) Token {
	str := readString(ctx, r)

	if str != nil {
		return Token{Data: string(str), Type: StringToken}
	}
	ctx.writeBuffer.Reset()
	readRunes(r, ctx.writeBuffer, func(x rune) bool { return !(unicode.IsSpace(x) || x == ')' || x == '(') })
	b := ctx.writeBuffer.Bytes()
	if len(b) == 0 {
		return Token{Type: None}
	}
	return Token{Data: string(b), Type: SymbolToken}
}

type WriteBuffer interface {
	Reset()
	WriteRune(r rune) (size int, err error)
	Bytes() []byte
}

type Symbol struct {
	Name string
}

func (s Symbol) String() string {
	return s.Name
}

type SymbolTable struct {
	Symbols map[string]*WeakRef
}

func (s *SymbolTable) GetOrCreate(key string) *Symbol {

	v, ok := s.Symbols[key]
	if ok {
		value, ok := v.GetTarget().(*Symbol)
		if ok {
			return value
		}

	}
	r := &Symbol{Name: key}
	s.Symbols[key] = NewWeakRef(r)
	return r
}
func (s *SymbolTable) Get(key string) *Symbol {

	v, ok := s.Symbols[key]
	if ok {
		value, ok := v.GetTarget().(*Symbol)
		if ok {
			return value
		}
	}
	return nil

}

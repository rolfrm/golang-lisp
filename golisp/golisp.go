package golisp

import (
	"bufio"
	"bytes"
	"fmt"
	"log"
	"os"
	"reflect"
	"strconv"
	"strings"
	"unicode"
)

type LispValue interface{}

type cons struct {
	Car LispValue
	Cdr LispValue
}

func Cons(a, b LispValue) *cons {
	return &cons{Car: a, Cdr: b}
}

func (c *cons) String() string {
	var sb strings.Builder
	sb.WriteString("(")
	for {
		sb.WriteString(fmt.Sprint(c.Car))
		if c.Cdr == nil {
			sb.WriteString(")")
			break
		}
		n, ok := c.Cdr.(*cons)
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

func Car(a LispValue) LispValue {
	v, ok := a.(*cons)
	if ok {
		return v.Car
	}
	return nil
}
func Cdr(a LispValue) LispValue {
	if a == nil {
		return nil
	}
	v, e := a.(*cons)
	if e {
		return v.Cdr
	}
	return nil
}
func Caddr(a LispValue) LispValue {
	return Car(Cddr(a))

}
func Cadddr(a LispValue) LispValue {
	return Car(Cdddr(a))
}
func Cadr(a LispValue) LispValue {
	return Car(Cdr(a))
}
func Cddr(a LispValue) LispValue {
	return Cdr(Cdr(a))
}
func Cdddr(a LispValue) LispValue {
	return Cdr(Cddr(a))
}

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

func (l *LispContext) GetOrCreateSymbol(key string) *Symbol {
	return l.Symbols.GetOrCreate(key)
}

func (lisp *LispContext) Defbuiltin(name string, f func(values LispValue) LispValue) {
	sym := lisp.Symbols.GetOrCreate(name)
	lisp.Globals.Scope[sym] = Builtin{Invoke: f}
}

func (lisp *LispContext) Defbuiltin0(name string, f func() LispValue) {
	sym := lisp.Symbols.GetOrCreate(name)
	lisp.Globals.Scope[sym] = f
}

func (lisp *LispContext) Defbuiltin1(name string, f func(values LispValue) LispValue) {
	sym := lisp.Symbols.GetOrCreate(name)
	lisp.Globals.Scope[sym] = f
}

func (lisp *LispContext) Defbuiltin2(name string, f func(a, b LispValue) LispValue) {
	sym := lisp.Symbols.GetOrCreate(name)
	lisp.Globals.Scope[sym] = f
}

func (lisp *LispContext) Register(name string, f interface{}) {
	sym := lisp.Symbols.GetOrCreate(name)
	lisp.Globals.Scope[sym] = f
}

func DefbuiltinAcc[T any](lisp *LispContext, name string, f func(b, a T) T) {
	sym := lisp.Symbols.GetOrCreate(name)

	lisp.Globals.Scope[sym] = Builtin{Invoke: func(values LispValue) LispValue {
		var acc T = Car(values).(T)
		for i := Cdr(values); i != nil; i = Cdr(i) {
			acc = f(acc, Car(i).(T))
		}
		return acc
	}}
}

type Number interface {
	int64 | float64
}

func fixTypes(a, b LispValue) (LispValue, LispValue) {
	switch v := a.(type) {
	case int64:
		switch v2 := b.(type) {
		case int64:
			return v, v2
		case float64:
			return float64(v), v2
		}
	case float64:
		switch v2 := b.(type) {
		case int64:
			return v, float64(v2)
		case float64:
			return v, v2
		}
	}
	return a, b
}

func genAdd(a, b LispValue) LispValue {
	a, b = fixTypes(a, b)
	switch v := a.(type) {
	case int64:
		return v + b.(int64)
	case float64:
		return v + b.(float64)
	}
	return a
}

func genSub(a, b LispValue) LispValue {
	a, b = fixTypes(a, b)
	switch v := a.(type) {
	case int64:
		return v - b.(int64)
	case float64:
		return v - b.(float64)
	}
	return a
}
func genMul(a, b LispValue) LispValue {
	a, b = fixTypes(a, b)
	switch v := a.(type) {
	case int64:
		return v * b.(int64)
	case float64:
		return v * b.(float64)
	}
	return a
}
func genDiv(a, b LispValue) LispValue {
	a, b = fixTypes(a, b)
	switch v := a.(type) {
	case int64:
		return v / b.(int64)
	case float64:
		return v / b.(float64)
	}
	return a
}
func genLt(a, b LispValue) LispValue {
	a, b = fixTypes(a, b)
	switch v := a.(type) {
	case int64:
		if v < b.(int64) {
			return true
		}
		return nil
	case float64:
		if v < b.(float64) {
			return true
		}
		return nil
	}
	return a
}

func genGt(a, b LispValue) LispValue {
	a, b = fixTypes(a, b)
	switch v := a.(type) {
	case int64:
		if v > b.(int64) {
			return true
		}
		return nil
	case float64:
		if v > b.(float64) {
			return true
		}
		return nil
	}
	return a
}

func NewLispContext() LispContext {
	lisp := LispContext{
		Globals: NewLispScope(),
		Symbols: SymbolTable{
			Symbols: make(map[string]*WeakRef)}}

	DefbuiltinAcc(&lisp, "+", genAdd)
	DefbuiltinAcc(&lisp, "*", genMul)
	DefbuiltinAcc(&lisp, "-", genSub)
	DefbuiltinAcc(&lisp, "/", genDiv)

	test := func(r bool) LispValue {
		if r {
			return r
		}
		return nil
	}

	lisp.Defbuiltin2("<", genLt)
	lisp.Defbuiltin2(">", genGt)
	lisp.Defbuiltin2("=", func(x, y LispValue) LispValue { return test(x == y) })

	lisp.Defbuiltin2("cons", func(x, y LispValue) LispValue { return Cons(x, y) })
	lisp.Defbuiltin1("car", func(x LispValue) LispValue { return Car(x) })
	lisp.Defbuiltin1("cdr", func(x LispValue) LispValue { return Cdr(x) })
	lisp.Defbuiltin1("cadr", Cadr)
	lisp.Defbuiltin1("caddr", Caddr)
	lisp.Defbuiltin1("cadddr", Cadddr)
	lisp.Defbuiltin1("print", func(x LispValue) LispValue { fmt.Print(x, "\n"); return x })
	lisp.Defbuiltin1("error", func(x LispValue) LispValue { log.Panic(x); return x })
	lisp.Defbuiltin("type-of", func(x LispValue) LispValue { return reflect.TypeOf(x) })
	log.Println("make hashtable")
	lisp.Register("make-hashtable", func() map[LispValue]LispValue {
		return make(map[LispValue]LispValue)
	})

	lisp.Defbuiltin1("load", func(path LispValue) LispValue {
		return lisp.EvalFile(path.(string))
	})

	lisp.Globals.Scope[lisp.Symbols.GetOrCreate("nil")] = nil
	lisp.Globals.Scope[lisp.Symbols.GetOrCreate("quote")] = MacroFunction{
		function: func(x LispValue) LispValue { return x },
		varadic:  true,
	}

	return lisp
}

type MacroFunction struct {
	function LispValue
	varadic  bool
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

func (l *LispContext) EvalString(str string) LispValue {
	rd := strings.NewReader(str)
	return l.EvalStream(bufio.NewReader(rd))
}

func (l *LispContext) EvalFile(file string) LispValue {
	rd, e := os.Open(file)
	if e != nil {
		return e
	}
	return l.EvalStream(bufio.NewReader(rd))
}

func (lisp *LispContext) ReadToken(token Token) LispValue {
	switch token.Type {
	case None:
		return nil
	case StringToken:
		return string(token.Data)
	case ListToken:
		var c []*cons = make([]*cons, len(token.SubTokens))

		for i, x := range token.SubTokens {
			c[i] = Cons(lisp.ReadToken(x), nil)
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

type Lambda *cons

func (lisp *LispContext) EvalStream(r *bufio.Reader) LispValue {
	ctx := ParserContext{}

	ctx.writeBuffer = bytes.NewBuffer(make([]byte, 1))
	var result LispValue
	for {
		t := TokenizeStream(ctx, r)
		if t.Type == None {
			return result
		}
		t2 := lisp.ReadToken(t)
		for {

			t3 := lisp.MacroExpand(&lisp.Globals, t2)
			if t2 == t3 {
				break
			}
			t2 = t3
		}
		result = EvalLisp(&lisp.Globals, t2)
		if t.Type == None {
			break
		}
	}
	return result
}

func (l *LispScope) Let(argForm LispValue) *LispScope {
	ctx2 := l.SubScope()
	return ctx2
}

type LambdaFunction struct {
	scope *LispScope
	body  LispValue
	args  *cons
}

func (lisp *LispContext) MacroExpandCons(scope *LispScope, c *cons) *cons {
	r := lisp.MacroExpand(scope, Car(c))
	next, ok := c.Cdr.(*cons)
	if ok {
		exp := lisp.MacroExpandCons(scope, next)
		if exp == next && r == Car(c) {
			return c
		}
		return Cons(r, exp)
	} else if r == Car(c) {
		return c
	}
	return Cons(r, nil)
}

func (lisp *LispContext) MacroExpand(scope *LispScope, v LispValue) LispValue {
	cns, ok := v.(*cons)
	if !ok {
		return v
	}
	cns = lisp.MacroExpandCons(scope, cns)

	fst := Car(cns)
	sym, ok := fst.(*Symbol)
	if !ok {
		return cns
	}
	if ok {
		m, ok := scope.GetValue(sym).(MacroFunction)
		if !ok {
			return cns
		}
		l, ok := m.function.(LambdaFunction)
		if !ok {
			return cns
		}
		if ok {
			scope2 := l.scope.SubScope()
			args2 := l.args

			if args2 != nil { // nil as LispValue is different from nil
				var args3 LispValue = args2

				for a, j := args3, Cdr(cns).(LispValue); a != nil && j != nil; a, j = Cdr(a), Cdr(j) {
					t1, t2 := Car(a).(*Symbol), Car(j)
					if t1.Name == "&rest" {
						t1 = Cadr(a).(*Symbol)
						t2 = j
						scope2.OverwriteValue(t1, t2)
						break
					} else {
						scope2.OverwriteValue(t1, t2)
					}
				}
			}

			var result LispValue
			for bodyIt := l.body; bodyIt != nil; bodyIt = Cdr(bodyIt) {
				result = EvalLisp(scope2, Car(bodyIt))
			}
			return result
		}
	}
	return cns
}

func EvalLisp(scope *LispScope, v LispValue) LispValue {
	cns, ok := v.(*cons)
	if !ok { // not a cons -> just return the value
		sym, ok := v.(*Symbol)
		if ok {
			return scope.GetValue(sym)
		}
		return v
	}

	fst := Car(cns)
	sym, ok := fst.(*Symbol)
	if ok {
		if sym.Name == "lambda" {
			args, ok := Cadr(cns).(*cons)
			body, ok2 := Cddr(cns).(*cons)
			if args != nil && !ok {
				log.Fatal("args")
			}
			if !ok2 {
				log.Fatal("body")
			}
			return LambdaFunction{args: args, body: body, scope: scope}
		}
		if sym.Name == "let" {
			argForm := Cadr(cns)
			bodyForm := Cddr(cns)
			scope2 := scope.Let(argForm)
			for i := argForm; i != nil; i = Cdr(i) {
				nv := Car(i).(*cons)
				name := Car(nv).(*Symbol)
				value := EvalLisp(scope2, Cadr(nv))
				scope.OverwriteValue(name, value)
			}
			var r LispValue = nil
			for i := bodyForm; i != nil; i = Cdr(i) {
				r = EvalLisp(scope2, Car(i))
			}
			return r
		}
		if sym.Name == "set" || sym.Name == "define" {
			name := Cadr(cns)
			value := Caddr(cns)

			r := EvalLisp(scope, value)
			if sym.Name == "define" {
				scope.TopScope().OverwriteValue(name.(*Symbol), r)
			} else {
				scope.SetValue(name.(*Symbol), r)
			}
			return r
		}
		if sym.Name == "progn" {
			var r LispValue = nil
			for i := Cdr(cns); i != nil; i = Cdr(i) {
				r = EvalLisp(scope, Car(i))
			}
			return r
		}
		if sym.Name == "if" {
			testForm := Cadr(cns)
			trueForm := Caddr(cns)
			falseForm := Cadddr(cns)
			test := EvalLisp(scope, testForm)
			if test == nil {
				return EvalLisp(scope, falseForm)
			}
			return EvalLisp(scope, trueForm)
		}
		if sym.Name == "loop" {
			testForm := Cadr(cns)
			evalForm := Cddr(cns)
			var r LispValue = nil
			for EvalLisp(scope, testForm) != nil {
				for i := evalForm; i != nil; i = Cdr(i) {
					r = EvalLisp(scope, Car(i))
				}
			}
			return r
		}
		if sym.Name == "quote" {
			return Cadr(cns)
		}
		if sym.Name == "macro" {
			body := Cadr(cns)
			lambda, ok := EvalLisp(scope, body).(LambdaFunction)
			if !ok {
				log.Fatal("Body of macro must be a lambda")
			}
			return MacroFunction{
				function: lambda,
			}
		}
	}

	var rest LispValue = cns
	args := []*cons{}
	for j, i := 0, rest; i != nil; j, i = j+1, Cdr(i) {
		arg := EvalLisp(scope, Car(i))

		args = append(args, Cons(arg, nil))
		if j > 0 {
			args[j-1].Cdr = args[j]
		}
	}

	fval := Car(args[0])
	b, ok := fval.(Builtin)
	if ok {
		return b.Invoke(args[1])
	}
	l, ok := fval.(LambdaFunction)

	if ok {
		scope2 := l.scope
		args2 := l.args

		if args2 != nil { // nil as LispValue is different from nil

			var args3 LispValue = args2
			args4, ok := Cdr(args[0]).(LispValue)
			if ok {
				scope2 = scope2.SubScope()

				for a, j := args3, args4; a != nil && j != nil; a, j = Cdr(a), Cdr(j) {
					t1, t2 := Car(a).(*Symbol), Car(j)
					if t1.Name == "&rest" {
						t1 = Cadr(a).(*Symbol)
						t2 = j
						scope2.OverwriteValue(t1, t2)
						break
					} else {
						scope2.OverwriteValue(t1, t2)
					}
				}
			}
		}

		var result LispValue
		for bodyIt := l.body; bodyIt != nil; bodyIt = Cdr(bodyIt) {
			result = EvalLisp(scope2, Car(bodyIt))
		}
		return result
	}

	switch len(args) {
	case 1:
		f, ok := fval.(func() LispValue)
		if ok {
			return f()
		}
		break
	case 2:
		f, ok := fval.(func(LispValue) LispValue)
		if ok {
			return f(Car(args[1]))
		}
		break
	case 3:
		f, ok := fval.(func(a, b LispValue) LispValue)
		if ok {
			return f(Car(args[1]), Car(args[2]))
		}
		break
	default:
		log.Fatal("Unsupported number of args.")
	}

	values := make([]reflect.Value, len(args)-1)
	for i, v := range args[1:] {
		values[i] = reflect.ValueOf(Car(v))
	}

	r := reflect.ValueOf(fval).Call(values)
	if len(r) > 0 {
		return r[0].Interface()
	}
	return nil
}

func TokenizeStream(ctx ParserContext, r *bufio.Reader) Token {
	skipCommentAndWhiteSpace(ctx, r)
	rune, _, _ := r.ReadRune()

	if rune == '(' {
		lst := []Token{}
		for {

			tk := TokenizeStream(ctx, r)
			skipCommentAndWhiteSpace(ctx, r)
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

func skipCommentAndWhiteSpace(ctx ParserContext, r *bufio.Reader) {
	ctx.writeBuffer.Reset()
	for {
		start := len(ctx.writeBuffer.Bytes())
		readRunes(r, ctx.writeBuffer, func(x rune) bool { return unicode.IsSpace(x) })
		if peekRune(r) == ';' {
			readRunes(r, ctx.writeBuffer, func(x rune) bool { return x != '\n' })
		}
		end := len(ctx.writeBuffer.Bytes())
		if start == end {
			break
		}
	}
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
	readRunes(r, ctx.writeBuffer, func(x rune) bool { return !(unicode.IsSpace(x) || x == ')' || x == '(' || x == ';') })
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

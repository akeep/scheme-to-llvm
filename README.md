Scheme-to-LLVM
=================

The `scheme-to-llvm` compiler is a compiler from a small subset of Scheme to
[LLVM](http://llvm.org)'s assembly form intermediate representation.  The
compiler was original developed for an invited workshop at
2020 edition of the European Lisp Symposium:
[ELS2020](https://european-lisp-symposium.org/2020/index.html), and you can
find slides for the talk and a link to the presentation video.  The compiler is
based on a student compiler written to use the nanopass framework, but
enhanced to use some of the techniques from Chez Scheme, which is also the
host compiler.

Source Language
----------------

```
Expr -> <x>
      | <imm>
      | (quote <d>)
      | (if <Expr> <Expr>)
      | (if <Expr> <Expr> <Expr>)
      | (and <Expr>* ...)
      | (or <Expr>* ...)
      | (not <Expr>)
      | (set! <x> <Expr>)
      | (begin <Expr>* ... <Expr>)
      | (lambda (<x>* ...) <Expr>* ... <Expr>)
      | (let ([<x>* <Expr>*] ...) <Expr>* ... <Expr>)
      | (letrec ([<x>* <Expr>*] ...) <Expr>* ... <Expr>)
      | (<Expr> <Expr>* ...)
      | (<pr> <Expr>* ...)
```

Where `x` is a variable, `imm` is an immediate, `d` is a Scheme datum in our
target language, and `pr` is a primitive.

- An immediate is a signed 60-bit integer (fixnum), a boolean (`#t` or `#f`),
  or null (`'()`).
- Datum is a pair of datum, a vector of datum, or an immediate
- Variables are represented as Scheme symbols.
- Primitives are also represented as Scheme symbols, though they are limited to
  the following table:

| *primitive*     | *arity* | *argument types*    | *return type* |
| --------------- | ------- | ------------------- | --------------|
| `+`             | 2       | fixnum, fixnum      | fixnum        |
| `-`             | 2       | fixnum, fixnum      | fixnum        |
| `*`             | 2       | fixnum, fixnum      | fixnum        |
| `cons`          | 2       | any, any            | pair          |
| `pair?`         | 1       | any                 | boolean       |
| `car`           | 1       | pair                | any           |
| `set-car!`      | 2       | pair, any           | void          |
| `cdr`           | 1       | pair                | any           |
| `set-cdr!`      | 2       | pair, any           | void          |
| `make-vector`   | 1       | fixnum              | vector        |
| `vector?`       | 1       | any                 | boolean       |
| `vector-length` | 1       | vector              | fixnum        |
| `vector-ref`    | 2       | vector, fixnum      | any           |
| `vector-set!`   | 3       | vector, fixnum, any | void          |
| `void`          | 0       |                     | void          |
| `<`             | 2       | fixnum, fixnum      | boolean       |
| `<=`            | 2       | fixnum, fixnum      | boolean       |
| `=`             | 2       | fixnum, fixnum      | boolean       |
| `>=`            | 2       | fixnum, fixnum      | boolean       |
| `>`             | 2       | fixnum, fixnum      | boolean       |
| `eq?`           | 2       | any, any            | boolean       |
| `boolean?`      | 1       | any                 | boolean       |
| `fixnum?`       | 1       | any                 | boolean       |
| `null?`         | 1       | any                 | boolean       |
| `procedure?`    | 1       | any                 | boolean       |


Building and Using the Compiler
--------------------------------

In order to run the compiler you need the following dependencies:

- LLVM w/Clang installed
  - If you have LLVM/Clang 10 installed you can use the set the parameter
    `use-llvm-10-tailcc` to `#t` to use the `tailcc` calling convention added
    in LLVM 10
- Chez Scheme: https://github.com/cisco/ChezScheme
- The nanopas framework: https://github.com/nanopass/nanopass-framework-scheme

With those installed, you can load compiler into Chez Scheme as follows
(assuming you are starting from the `scheme-to-llvm` directory).

```
$ scheme --libdirs <path-to-nanopass-framework>:src/main/scheme
Chez Scheme Version 9.5.3
Copyright 1984-2019 Cisco Systems, Inc.

> (import (c))  ;; import the example compiler
> (tiny-compile
    '(letrec ([factorial (lambda (n)
                           (if (= n 0)
                               1
                               (* n (factorial (- n 1)))))])
       (factorial 10)))
3628800
```

Note that under the covers the `tiny-compile` produces a file called `t.ll`,
uses `clang` to compile and link this LLVM IR code into an executable in `t`.
This application writes the result of the program to a temporary output file,
and `tiny-compile` uses the Chez Scheme reader to pull read the result.

Testing
--------

There is also a set of tests included in the compiler (originally from the
student compiler), which you can run with `test-all` or `analyze-all`.
`test-all` will run all of the tests until one fails, while `analyze-all` will
run all of the tests and print `.` for successful tests, `F` for tests that
produced the incorrect results and `E` for tests that raised an exception.
Optionally `test-all` can also be passed a boolean to indicate if it should be
_noisy_, which when `#t` will print each test as it begins compiling and
running it.

Finally, passes can be traced with the `traced-passes` parameter, any pass that
is traced will print the output produced by the pass.  `traced-passes` attempts
to be flexible in specifying the passes:

- `(traced-passes 'pass-name)` will add `'pass-name` to the list of traced
  passes if it is not in the list, or remove it from the list if it already is;
- `(traced-passes '(pass-name1 pass-name2 ... pass-nameN))` is equivalent to
  calling `trace-passes` on each `'pass-nameJ`;
- `(traced-passes '())` or `(traced-passes #f)` clears all tracing;
- `(traced-passes #t)` traces all passes; and
- `(traced-passes)` returns the current list of passes.

You can see the full list of passes by referencing the variable `all-passes`

Source Layout
--------------

The source layout is very simple in this example compiler.  All of the source
code is in the `src/main/scheme` directory.  The entire compiler and tests are
in the file `c.sls`.  The `parse-scheme` pass makes use of the s-expression
pattern matcher defined in `match.sls`, and various parts of the compiler make
use of some of the type and primitive definitions in `d.sls`.  If you look at
`d.sls` you'll notice there are a number of data types and primitives not
supported in the current compiler.  This was a very simple start at building a
more complete Scheme implementation, but is, as of yet, unimplemented.


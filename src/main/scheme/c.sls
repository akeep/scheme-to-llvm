#!chezscheme
(library (c)
  (export
    datum?
    make-var var var? var-name var-unique-name var-flags var-flags-referenced?
    var-flags-referenced-set! var-flags-assigned? var-flags-assigned-set!
    var-flags-multiply-referenced? var-flags-multiply-referenced-set!
    var-flags-multiply-assigned? var-flags-multiply-assigned-set!
    Lsrc unparse-Lsrc parse-Lsrc
    parse-scheme
    Ldatum unparse-Ldatum 
    convert-complex-datum
    uncover-assigned!
    Lletrec unparse-Lletrec
    purify-letrec
    Lno-assign unparse-Lno-assign
    convert-assignments
    optimize-direct-call
    remove-anonymous-lambda
    Lsanitized unparse-Lsanitized
    sanitize-binding-forms
    Lfree unparse-Lfree
    uncover-free
    make-label label label? label-name label-unique-name label-slot label-slot-set!
    make-local-label local-label?
    Lclosure unparse-Lclosure
    convert-closures
    optimize-known-call
    introduce-procedure-primitives
    Llifted unparse-Llifted
    lift-letrec
    Lnormalized unparse-Lnormalized
    normalize-context
    Lrep unparse-Lrep
    specify-representation
    Llocals unparse-Llocals
    uncover-locals
    Lno-let unparse-Lno-let
    remove-let
    Lsimple-opnd unparse-Lsimple-opnd
    remove-complex-opera*
    Lflat-set! unparse-Lflat-set!
    flatten-set!
    Lbb unparse-Lbb
    expose-basic-blocks
    optimize-blocks-reorders
    optimize-blocks
    Lssa unparse-Lssa
    convert-to-ssa
    Lflat-funcs unparse-Lflat-funcs
    flatten-functions
    generate-llvm-code
    tiny-compile
    all-passes
    traced-passes
    tests
    test-all
    analyze-all
    use-llvm-10-tailcc
    )
  (import (except (rnrs) with-output-to-file current-output-port flush-output-port)
          (nanopass)
          ;; for experimental testing only
          ; (except (nanopass) define-language)
          ; (rename (nanopass exp-syntax) (define-language-exp define-language))
          (match) (d)
    (only (chezscheme) trace-define trace-define-syntax trace-let trace-lambda
          format enumerate iota errorf fluid-let module with-implicit datum
          trace-define-syntax make-list printf pretty-print make-parameter
          void parameterize with-output-to-file current-output-port system eval flush-output-port))

  (define use-llvm-10-tailcc (make-parameter #f (lambda (x) (and x #t))))

  ;;; helpers for the scheme-dependent portion of the compiler
  (define word-shift 3) ; 64-bit words
  (define word-size (expt 2 word-shift))

  (define fixnum-bits 61)
  (define shift-fixnum 3)
  (define mask-fixnum #b111)
  (define tag-fixnum #b000)

  (define mask-pair #b111)
  (define tag-pair #b001)
  (define size-pair 16)
  (define disp-car 0)
  (define disp-cdr 8)

  (define mask-vector #b111)
  (define tag-vector  #b011)
  (define disp-vector-length 0)
  (define disp-vector-data 8)

  (define mask-procedure #b111)
  (define tag-procedure  #b010)
  (define disp-procedure-code 0)
  (define disp-procedure-data 8)

  (define mask-boolean   #b11110111)
  (define tag-boolean    #b00000110)

  (define $false         #b00000110)
  (define $true          #b00001110)
  (define $nil           #b00010110)
  (define $void          #b00011110)

  (define fixnum-range?
    (lambda (n)
      (<= (- (expt 2 (- fixnum-bits 1)))
          n
          (- (expt 2 (- fixnum-bits 1)) 1))))

  (define datum? (lambda (x) (datatype? x)))

  ;; utility for keeping our begins flat
  (define-syntax define-begin-builder
    (lambda (x)
      (syntax-case x (begin unquote)
        [(_ name [(lang nt) (begin ,e* dots ,e)])
         (eq? (datum dots) '...)
         #'(define-pass name : (lang nt) (e* e) -> (lang nt) ()
             (definitions
               (define (E* e* flat-e*)
                 (let f ([e* e*])
                   (if (null? e*)
                       flat-e*
                       (let ([e (car e*)] [e* (cdr e*)])
                         (nt e (f e*)))))))
             (nt : nt (ir flat-e*) -> * (flat-e*)
               [(begin ,e* (... ...) ,e) (E* e* (nt e flat-e*))]
               [else (cons ir flat-e*)])
             (let ([flat-e* (E* e* (nt e '()))])
               (let loop ([e (car flat-e*)] [e* (cdr flat-e*)] [re* '()])
                 (if (null? e*)
                     (if (null? re*)
                         e
                         (with-output-language (lang nt)
                           `(begin ,(reverse re*) (... ...) ,e)))
                     (loop (car e*) (cdr e*) (cons e re*))))))]
        [(_ name [(ef-lang ef-nt) (begin ,ef0* dots0 ,ef)] [(x-lang x-nt) (begin ,ef1* dots1 ,x)])
         (and (eq? (datum dots0) '...) (eq? (datum dots1) '...))
         #'(define-pass name : (ef-lang ef-nt) (ef* x) -> (x-lang x-nt) ()
             (definitions
               (define (Ef* ef* flat-ef*)
                 (let f ([ef* ef*])
                   (if (null? ef*)
                       flat-ef*
                       (ef-nt (car ef*) (f (cdr ef*)))))))
             (ef-nt : ef-nt (ir flat-ef*) -> * (flat-ef*)
               [(begin ,ef0* (... ...) ,ef) (Ef* ef0* (ef-nt ef flat-ef*))]
               [else (cons ir flat-ef*)])
             (x-nt : x-nt (ir) -> x-nt (ef*)
               [(begin ,ef1* (... ...) ,[x flat-ef*])
                (values x (Ef* ef1* flat-ef*))]
               [else (values ir '())])
             (let-values ([(x flat-ef*) (x-nt x)])
               (let ([flat-ef* (Ef* ef* flat-ef*)])
                 (if (null? flat-ef*)
                     x
                     (with-output-language (x-lang x-nt)
                       `(begin ,flat-ef* (... ...) ,x))))))])))

  (define-record-type var
    (nongenerative)
    (fields name (mutable unique-name $var-unique-name var-unique-name-set!) (mutable flags) (mutable slot))
    (protocol
      (lambda (new)
        (lambda (name)
          (new (if (var? name) (var-name name) name) #f 0 #f)))))

  (define var-unique-name
    (let ([c 0])
      (lambda (x)
        (or ($var-unique-name x)
            (let ([un (string->symbol (format "~s.~s" (var-name x) c))])
              (set! c (fx+ c 1))
              (var-unique-name-set! x un)
              un)))))

  (define-syntax define-flags-field
    (lambda (x)
      (define format-id
        (lambda (tid fmt . args)
          (datum->syntax tid
            (string->symbol
              (apply format fmt (map syntax->datum args))))))
      (syntax-case x ()
        [(_ dt fld flags ...)
         (with-syntax ([getter (format-id #'dt "~s-~s" #'dt #'fld)]
                       [setter (format-id #'dt "~s-~s-set!" #'dt #'fld)]
                       [(index ...) (enumerate #'(flags ...))]
                       [(flag-getter* ...) (map (lambda (flag) (format-id #'dt "~s-~s-~s?" #'dt #'fld flag)) #'(flags ...))]
                       [(flag-setter* ...) (map (lambda (flag) (format-id #'dt "~s-~s-~s-set!" #'dt #'fld flag)) #'(flags ...))]
                       [bitset? (if (< (length #'(flags ...)) (- (fixnum-width) 1)) #'fxbit-set? #'bitwise-bit-set?)]
                       [bitcopy (if (< (length #'(flags ...)) (- (fixnum-width) 1)) #'fxcopy-bit #'bitwise-copy-bit)])
           #'(begin
               (define flag-getter*
                 (lambda (x)
                   (bitset? (getter x) index)))
               ...
               (define flag-setter*
                 (lambda (x set?)
                   (setter x (bitcopy (getter x) index (if set? 1 0)))))
               ...))])))

  (define-flags-field var flags referenced assigned multiply-referenced multiply-assigned)

  (define-language Lsrc
    (terminals
      (datum (d))
      (var (x)) => var-unique-name
      (primitive-info (pr)) => primitive-info-name)
    (Expr (e)
      x
      (quote d)
      (if e0 e1 e2)
      (begin e* ... e)
      (set! x e)
      (lambda (x* ...) e)
      (let ([x* e*] ...) e)
      (letrec ([x* e*] ...) e)
      (callable e* ...))
    (Callable (callable)
      e
      pr))

  (define-parser parse-Lsrc Lsrc)

  (define void-pr (primitive->primitive-info 'void))
  (define cons-pr (primitive->primitive-info 'cons))
  (define car-pr (primitive->primitive-info 'car))
  (define set-car!-pr (primitive->primitive-info 'set-car!))

  (define-pass parse-scheme : * (ir) -> Lsrc ()
    (definitions
      (module (empty-env extend-env extend-var-env extend-var-env* extend-primitive-syntax extend-primitive-syntax* apply-env)
        (define (empty-env) '())
        (define primitive->primitive-transformer
          (let ()
            (define t* '())
            (lambda (x)
              (cond
                [(assq x t*) => cdr]
                [else (let ([t (let ([info (primitive->primitive-info x)])
                                 (case-lambda [(env x)
                                   (match x
                                     [,sym (guard (symbol? sym)) (errorf who "primitives are currently only supported in call position")]
                                     [(,pr ,e* ...)
                                      (unless (eq? (primitive-info-name info) pr) (errorf who "attempting to apply primitive transformer for ~s to call of ~s" (primitive-info-name info) pr))
                                      (unless (arity-matches? info e*) (errorf who "incorrect number of arguments ~s" (length e*)))
                                      (with-output-language (Lsrc Expr) `(,info ,(parse* e* env) ...))]
                                     [(set! ,x ,e) (errorf who "primitives are immutable, ~s cannot be modified with set!" x)]
                                     [,x (errorf who "unexpected syntax ~s" x)])]
                                              [any (errorf who "got ~s arguments ~s, expected 2" (length any) any)]))])
                        (set! t* (cons (cons x t) t*))
                        t)]))))
        (define-syntax extend-primitive-syntax
          (lambda (x)
            (define (rewrite-rest rest)
              (syntax-case rest ()
                [() rest]
                [dots (eq? (datum dots) '...) #'dots]
                [id (identifier? #'id) #',id]
                [(a . d) (with-syntax ([a (rewrite-rest #'a)] [d (rewrite-rest #'d)]) #'(a . d))]))
            (define process-cl 
              (lambda (name)
                (with-syntax ([name name])
                  (lambda (cl)
                    (syntax-case cl (set!)
                      [[id . body]
                       (identifier? #'id)
                       #'[,sym (guard (eq? sym 'name)) . body]]
                      [[(set! x e) . body]
                       (and (identifier? #'x) (identifier? #'e))
                       #'[(set! ,x ,e) (guard (eq? x 'name)) . body]]
                      [[(_ . rest) . body]
                       (with-syntax ([rest (rewrite-rest #'rest)])
                         #'[(name . rest) . body])])))))
            (syntax-case x ()
              [(k name ct-env cl* ...)
               (with-implicit (k env)
                 (with-syntax ([(cl* ...) (map (process-cl #'name) #'(cl* ...))])
                   #'(extend-env ct-env 'name
                       (lambda (env x)
                         (match x
                           cl* ...
                           [else (errorf who "invalid syntax ~s" x)])))))])))
        (define-syntax extend-primitive-syntax*
          (lambda (x)
            (syntax-case x ()
              [(k ct-env) #'ct-env]
              [(k ct-env [name cl* ...] . rest)
               (with-implicit (k extend-primitive-syntax extend-primitive-syntax*)
                 #'(extend-primitive-syntax name (extend-primitive-syntax* ct-env . rest) cl* ...))])))
        (define (make-var-transformer sym var)
          (lambda (env x)
            (with-output-language (Lsrc Expr)
              (match x
                [,id (guard (eq? id sym)) var]
                [(,id ,e* ...) (guard (eq? id sym)) `(,var ,(parse* e* env) ...)]
                [(set! ,id ,e) (guard (eq? id sym)) `(set! ,var ,(parse e env))]
                [else (errorf who "invalid syntax ~s" x)]))))
        (define (apply-env env x)
          (cond
            [(assq x env) => cdr]
            [(primitive? x) (primitive->primitive-transformer x)]
            [else (errorf who "~s is unbound" x)]))
        (define (extend-env env x transformer) (cons (cons x transformer) env))
        (define (extend-var-env env x var) (extend-env env x (make-var-transformer x var)))
        (define (extend-var-env* env x* var*) (fold-left extend-var-env env x* var*)))
      (with-output-language (Lsrc Expr)
        (define (make-begin e* e)
          (if (null? e*)
              e
              `(begin ,e* ... ,e)))
        (define initial-env
          (extend-primitive-syntax* (empty-env)
            (quote [(_ d) (unless (datum? d) (errorf who "expected datum, but got ~s" d)) `(quote ,d)])
            (if
              [(_ e0 e1) `(if ,(parse e0 env) ,(parse e1 env) (,void-pr))]
              [(_ e0 e1 e2) `(if ,(parse e0 env) ,(parse e1 env) ,(parse e2 env))])
            (and
              [(_) `(quote #t)]
              [(_ e) (parse e env)]
              [(_ e0 e1 . e*) `(if ,(parse e0 env) ,(parse (cons* 'and e1 e*) env) (quote #f))])
            (or
              [(_) `(quote #f)]
              [(_ e) (parse e env)]
              [(_ e0 e1 . e*)
               (let ([t (make-var 't)])
                 `(let ([,t ,(parse e0 env)])
                    (if ,t ,t ,(parse (cons* 'or e1 e*) env))))])
            (not
              [(_ e) `(if ,(parse e env) (quote #f) (quote #t))])
            (begin
              [(_ e* ... e) (make-begin (parse* e* env) (parse e env))])
            (lambda
              [(_ (x* ...) e* ... e)
               (let ([v* (map make-var x*)])
                 (let ([env (extend-var-env* env x* v*)])
                   `(lambda (,v* ...) ,(make-begin (parse* e* env) (parse e env)))))])
            (let
              [(_ ([x0* e0*] ...) e* ... e)
               (let ([v0* (map make-var x0*)])
                 (let ([e0* (parse* e0* env)])
                   (let ([env (extend-var-env* env x0* v0*)])
                     `(let ([,v0* ,e0*] ...) ,(make-begin (parse* e* env) (parse e env))))))])
            (letrec
              [(_ ([x0* e0*] ...) e* ... e)
               (let ([v0* (map make-var x0*)])
                 (let ([env (extend-var-env* env x0* v0*)])
                   `(letrec ([,v0* ,(parse* e0* env)] ...)
                      ,(make-begin (parse* e* env) (parse e env)))))])
            (set!
              [(_ x e)
               (let ([t (apply-env env x)])
                 (t env (list 'set! x e)))]))))
      (define (parse* e* env) (map (lambda (e) (parse e env)) e*)))
    (parse : * (x env) -> Expr ()
      (match x
        [,imm (guard (immediate? imm)) `(quote ,imm)]
        [,sym (guard (symbol? sym)) ((apply-env env sym) env x)]
        [(,sym . ,e*) (guard (symbol? sym)) ((apply-env env sym) env x)]
        [(,[e] ,[e*] ...) `(,e ,e* ...)]
        [else (errorf who "expected Expr, but got ~s" x)]))
    (parse ir initial-env))

  (define-language Ldatum
    (extends Lsrc)
    (terminals
      (- (datum (d)))
      (+ (immediate (i))))
    (Expr (e)
      (- (quote d))
      (+ (quote i))))

  (define-pass convert-complex-datum : Lsrc (ir) -> Ldatum ()
    (definitions
      (define datum-var*)
      (define datum-e*)
      (define build-prim
        (lambda (prim)
          (primitive->primitive-info prim)))
      (with-output-language (Ldatum Expr)
        (define build-let
          (lambda (x* e* e)
            (if (null? x*)
                e
                `(let ([,x* ,e*] ...) ,e))))
        (define build-begin
          (lambda (e* e)
            (if (null? e*)
                e
                `(begin ,e* ... ,e))))
        (define build-lambda
          (lambda (x* e)
            `(lambda (,x* ...) ,e)))
        (define convert-datum
          (lambda (d)
            (cond
              [(pair? d)
               (let ([var-a (make-var 'tmp-a)]
                     [var-d (make-var 'tmp-d)]
                     [e-a (convert-datum (car d))]
                     [e-d (convert-datum (cdr d))])
                 (build-let (list var-a var-d) (list e-a e-d) `(,(build-prim 'cons) ,var-a ,var-d)))]
              [(vector? d)
               (let ([n (vector-length d)])
                 (let ([i* (iota n)])
                   (let ([t* (map (lambda (i) (make-var (string->symbol (format "tmp-~s" i)))) i*)]
                         [e* (map (lambda (d) (convert-datum d)) (vector->list d))]
                         [t (make-var 'tmp-v)])
                     (build-let t* e*
                       (build-let (list t) (list `(,(build-prim 'make-vector) ',n))
                         (build-begin
                           (map (lambda (ti i) `(,(build-prim 'vector-set!) ,t ',i ,ti)) t* i*)
                           t))))))]
              [(immediate? d) `(quote ,d)])))))
    (Expr : Expr (ir) -> Expr ()
      [(quote ,d)
       (if (immediate? d)
           `(quote ,d)
           (let ([var (make-var 'tmp)] [e (convert-datum d)])
             (set! datum-var* (cons var datum-var*))
             (set! datum-e* (cons e datum-e*))
             var))])
    (fluid-let ([datum-var* '()] [datum-e* '()])
      (let ([ir (Expr ir)])
        (build-let datum-var* datum-e* ir))))

  ;; NB: the following pass should not need to return anything, but the current
  ;; framework makes it easier if it does.
  (define-pass uncover-assigned! : Ldatum (ir) -> Ldatum ()
    (Expr : Expr (ir) -> Expr ()
      [(set! ,x ,[e]) (var-flags-assigned-set! x #t) ir]))

  (define-language Lletrec
    (extends Ldatum)
    (Expr (e)
      (- (lambda (x* ...) e)
         (letrec ([x* e*] ...) e))
      (+ f
         (letrec ([x* f*] ...) e)))
    (Lambda (f)
      (+ (lambda (x* ...) e))))
         
  (define-pass purify-letrec : Ldatum (ir) -> Lletrec ()
    (Expr : Expr (ir) -> Expr ()
      (definitions
        (define (build-let x* e* body)
          (if (null? x*)
              body
              `(let ([,x* ,e*] ...) ,body)))
        (define (build-letrec x* f* body)
          (if (null? x*)
              body
              `(letrec ([,x* ,f*] ...) ,body)))
        (define (build-set! x* e* body)
          (if (null? x*)
              body
              (let ([ef* (map (lambda (x e) `(set! ,x ,e)) x* e*)])
                `(begin ,ef* ... ,body)))))
      [(letrec ([,x* ,e*] ...) ,[e])
       (let loop ([tx* x*] [e* e*] [xs* '()] [es* '()] [xl* '()] [el* '()] [xc* '()] [ec* '()])
         (if (null? tx*)
             (build-let xs* es*
               (build-letrec xl* el*
                 (build-let xc* (make-list (length ec*) `(,void-pr))
                   (build-set! xc* ec* e))))
             (let ([x (car tx*)] [e (car e*)])
               (cond
                 [(var-flags-assigned? x)
                  (loop (cdr tx*) (cdr e*) xs* es* xl* el* (cons x xc*) (cons (Expr e) ec*))]
                 [(lambda-expr? e)
                  (loop (cdr tx*) (cdr e*) xs* es* (cons x xl*) (cons (Expr e) el*) xc* ec*)]
                 [(simple-expr? e)
                  (loop (cdr tx*) (cdr e*) (cons x xs*) (cons (Expr e) es*) xl* el* xc* ec*)]
                 [else
                  (var-flags-assigned-set! x #t) ;; we made an unassigned variable assigned, mark it.
                  (loop (cdr tx*) (cdr e*) xs* es* xl* el* (cons x xc*) (cons (Expr e) ec*))]))))])
    (lambda-expr? : Expr (ir) -> * (boolean)
      [(lambda (,x* ...) ,e) #t]
      [else #f])
    (simple-expr? : Expr (ir) -> * (boolean)
      [(quote ,i) #t]
      [,x (not (var-flags-assigned? x))]
      [(begin ,e* ... ,e) (and (for-all simple-expr? e*) (simple-expr? e))]
      [(if ,e0 ,e1 ,e2) (and (simple-expr? e0) (simple-expr? e1) (simple-expr? e2))]
      [(,pr ,e* ...) (and (pure-primitive? pr) (for-all simple-expr? e*))]
      [else #f]))

  (define-language Lno-assign
    (extends Lletrec)
    (Expr (e)
      (- (set! x e))))

  (define-pass convert-assignments : Lletrec (ir) -> Lno-assign ()
    (definitions
      (define with-assigned
        (lambda (x* f)
          (let loop ([x* x*] [rx* '()] [rassigned-x* '()] [rnew-x* '()])
            (if (null? x*)
                (if (null? rassigned-x*)
                    (f (reverse rx*))
                    (f (reverse rx*) (reverse rassigned-x*) (reverse rnew-x*)))
                (let ([x (car x*)] [x* (cdr x*)])
                  (if (var-flags-assigned? x)
                      (let ([new-x (make-var x)])
                        (loop x* (cons new-x rx*) (cons x rassigned-x*) (cons new-x rnew-x*)))
                      (loop x* (cons x rx*) rassigned-x* rnew-x*)))))))
      (define convert-bindings
        (lambda (x* e)
          (with-assigned x*
            (case-lambda
              [(x*) (values x* (Expr e))]
              [(x* assigned-x* new-x*)
               (values x*
                 (with-output-language (Lno-assign Expr)
                   (let ([pr* (map (lambda (new-x) `(,cons-pr ,new-x (,void-pr))) new-x*)])
                     `(let ([,assigned-x* ,pr*] ...)
                        ,(Expr e)))))])))))
    (Lambda : Lambda (ir) -> Lambda ()
      [(lambda (,x* ...) ,e)
       (let-values ([(x* e) (convert-bindings x* e)])
         `(lambda (,x* ...) ,e))])
    (Expr : Expr (ir) -> Expr ()
      [,x (if (var-flags-assigned? x) `(,car-pr ,x) x)]
      [(set! ,x ,[e]) `(,set-car!-pr ,x ,e)]
      [(let ([,x* ,[e*]] ...) ,e)
       (let-values ([(x* e) (convert-bindings x* e)])
         `(let ([,x* ,e*] ...) ,e))]))

  (define-pass optimize-direct-call : Lno-assign (ir) -> Lno-assign ()
    (Expr : Expr (ir) -> Expr ()
      [((lambda (,x* ...) ,[e]) ,[e* -> e*] ...)
       (guard (fx=? (length x*) (length e*)))
       `(let ([,x* ,e*] ...) ,e)]))

  (define-pass remove-anonymous-lambda : Lno-assign (ir) -> Lno-assign ()
    (Expr : Expr (ir [needs-name? #t] [maybe-name #f]) -> Expr ()
      [,f (if needs-name?
              (let ([t (make-var (or maybe-name 'anon))]) `(letrec ([,t ,(Lambda f)]) ,t))
              (Lambda f))]
      [(let ([,x* ,e*] ...) ,e)
       (let ([e* (map (lambda (x e) (Expr e #f x)) x* e*)] [e (Expr e #t maybe-name)])
         `(let ([,x* ,e*] ...) ,e))])
    (Lambda : Lambda (ir) -> Lambda ()))

  (define-language Lsanitized
    (extends Lno-assign)
    (Expr (e)
      (- f)))

  (define-pass sanitize-binding-forms : Lno-assign (ir) -> Lsanitized ()
    (Expr : Expr (ir) -> Expr ()
      (definitions
        (define build-letrec
          (lambda (x* f* e)
            (if (null? x*)
                e
                `(letrec ([,x* ,f*] ...) ,e))))
        (define build-let
          (lambda (x* e* e)
            (if (null? x*)
                e
                `(let ([,x* ,e*] ...) ,e)))))
      [(let ([,x* ,e*] ...) ,[e])
       (let loop ([x* x*] [e* e*] [rlet-x* '()] [rlet-e* '()] [rrec-x* '()] [rrec-f* '()])
         (if (null? x*)
             (build-letrec (reverse rrec-x*) (reverse rrec-f*)
               (build-let (reverse rlet-x*) (reverse rlet-e*) e))
             (nanopass-case (Lno-assign Expr) (car e*)
               [,f (loop (cdr x*) (cdr e*) rlet-x* rlet-e* (cons (car x*) rrec-x*) (cons (Lambda f) rrec-f*))]
               [else (loop (cdr x*) (cdr e*) (cons (car x*) rlet-x*) (cons (Expr (car e*)) rlet-e*) rrec-x* rrec-f*)])))])
    (Lambda : Lambda (ir) -> Lambda ()))

  (define-language Lfree
    (extends Lsanitized)
    (Lambda (f)
      (- (lambda (x* ...) e))
      (+ (lambda (x* ...) frbody)))
    (FreeBody (frbody)
      (+ (free (x* ...) e))))

  (define-pass uncover-free : Lsanitized (ir) -> Lfree ()
    (definitions
      (define-record-type fv-info
        (nongenerative)
        (fields lid (mutable mask) (mutable fv*))
        (protocol
          (lambda (new)
            (lambda (index)
              (new index 0 '())))))
      (define (record-ref! x info)
        (let ([idx (var-slot x)])
          (unless idx (errorf who "~s referenced without being bound" (var-name x)))
          (when (fx<? idx (fv-info-lid info))
            (let ([mask (fv-info-mask info)])
              (unless (bitwise-bit-set? mask idx)
                (fv-info-mask-set! info (bitwise-copy-bit mask idx 1))
                (fv-info-fv*-set! info (cons x (fv-info-fv* info))))))))
      (define (set-offsets! x* index)
        (fold-left (lambda (index x) (var-slot-set! x index) (fx+ index 1)) index x*))
      (define ($with-offsets index x* p)
        (let ([index (set-offsets! x* index)])
          (let ([v (p index)])
            (for-each (lambda (x) (var-slot-set! x #f)) x*)
            v)))
      (define-syntax with-offsets
        (lambda (x)
          (syntax-case x ()
            [(_ (index ?x*) ?e ?es ...)
             (identifier? #'index)
             #'($with-offsets index ?x* (lambda (index) ?e ?es ...))]))))
    (Callable : Callable (e index fv-info) -> Callable ())
    (Expr : Expr (e index fv-info) -> Expr ()
      [,x (record-ref! x fv-info) x]
      [(let ([,x* ,[e*]] ...) ,e)
       (with-offsets (index x*)
         `(let ([,x* ,e*] ...) ,(Expr e index fv-info)))]
      [(letrec ([,x* ,f*] ...) ,e)
       (with-offsets (index x*)
         (let ([f* (map (lambda (f) (Lambda f index fv-info)) f*)]
               [e (Expr e index fv-info)])
           `(letrec ([,x* ,f*] ...) ,e)))])
    (Lambda : Lambda (e index outer-fv-info) -> Lambda ()
      [(lambda (,x* ...) ,e)
       (let ([fv-info (make-fv-info index)])
         (with-offsets (index x*)
           (let ([e (Expr e index fv-info)])
             (let ([fv* (fv-info-fv* fv-info)])
               (for-each (lambda (fv) (record-ref! fv outer-fv-info)) fv*)
               `(lambda (,x* ...) (free (,fv* ...) ,e))))))])
    (Expr ir 0 (make-fv-info 0)))

  (define-record-type label
    (nongenerative)
    (fields name (mutable unique-name $label-unique-name label-unique-name-set!) (mutable slot))
    (protocol
      (lambda (new)
        (lambda (name)
          (cond
            [(symbol? name) (new name #f #f)]
            [(string? name) (new (string->symbol name) #f #f)]
            [(var? name) (new (var-name name) #f #f)])))))

  (define-record-type local-label
    (nongenerative)
    (parent label)
    (protocol
      (lambda (pargs->new)
        (lambda (name)
          ((pargs->new name))))))

  (define label-unique-name
    (let ([c 0])
      (lambda (l)
        (or ($label-unique-name l)
            (let ([un (string->symbol (format "~s$~s" (label-name l) c))])
              (set! c (fx+ c 1))
              (label-unique-name-set! l un)
              un)))))

  (define-language Lclosure
    (extends Lfree)
    (terminals
      (+ (label (l)) => label-unique-name))
    (Expr (e)
      (- (letrec ([x* f*] ...) e))
      (+ l
         (letrec ([l* f*] ...) clbody)))
    (ClosureBody (clbody)
      (+ (closures ([x* l* x** ...] ...) e)))
    (Lambda (f)
      (- (lambda (x* ...) frbody))
      (+ (lambda (x* ...) bfrbody)))
    (FreeBody (frbody)
      (- (free (x* ...) e)))
    (BindFreeBody (bfrbody)
      (+ (bind-free (x x* ...) e))))

  (define-pass convert-closures : Lfree (ir) -> Lclosure ()
    (Expr : Expr (e) -> Expr ()
      [(letrec ([,x* ,[f* free**]] ...) ,[e])
       (let ([l* (map make-label x*)])
         `(letrec ([,l* ,f*] ...)
            (closures ([,x* ,l* ,free** ...] ...) ,e)))]
      [(,x ,[e*] ...) `(,x ,x ,e* ...)]
      [(,pr ,[e*] ...) `(,pr ,e* ...)]
      [(,[e] ,[e*] ...)
       (let ([t (make-var 'proc)])
         `(let ([,t ,e]) (,t ,t ,e* ...)))])
    (Lambda : Lambda (f) -> Lambda (x*)
      [(lambda (,x* ...) (free (,x0* ...) ,[e]))
       (let ([cp (make-var 'cp)])
         (values `(lambda (,cp ,x* ...) (bind-free (,cp ,x0* ...) ,e)) x0*))]
      ;; NB: should be unnecessary
      [(lambda (,x* ...) ,frbody) (errorf who "unreachable")]))

  (define-pass optimize-known-call : Lclosure (ir) -> Lclosure ()
    (Lambda : Lambda (f) -> Lambda ())
    (Expr : Expr (ir) -> Expr ()
      [(,x ,[e*] ...)
       (cond
         [(var-slot x) => (lambda (l) `(,l ,e* ...))]
         [else `(,x ,e* ...)])]
      [(letrec ([,l0* ,f*] ...)
         (closures ([,x* ,l* ,x** ...] ...) ,e))
       (for-each (lambda (x l) (var-slot-set! x l)) x* l*)
       (let ([f* (map Lambda f*)] [e (Expr e)])
         (for-each (lambda (x) (var-slot-set! x #f)) x*)
         `(letrec ([,l0* ,f*] ...)
            (closures ([,x* ,l* ,x** ...] ...) ,e)))]
      ;; NB: should be unnecessary
      [(letrec ([,l* ,f*] ...) ,clbody) (errorf who "unreachable")]))

  (define make-procedure-pr (primitive->primitive-info '$make-procedure))
  (define procedure-ref-pr (primitive->primitive-info '$procedure-ref))
  (define procedure-code-pr (primitive->primitive-info '$procedure-code))
  (define procedure-set!-pr (primitive->primitive-info '$procedure-set!))

  (define-language Lproc
    (extends Lclosure)
    (Expr (e)
      (- (letrec ([l* f*] ...) clbody))
      (+ (letrec ([l* f*] ...) e)))
    (ClosureBody (clbody)
      (- (closures ([x* l* x** ...] ...) e)))
    (Lambda (f)
      (- (lambda (x* ...) bfrbody))
      (+ (lambda (x* ...) e)))
    (BindFreeBody (bfrbody)
      (- (bind-free (x x* ...) e))))

  (define-pass introduce-procedure-primitives : Lclosure (ir) -> Lproc ()
    (definitions
      (define with-fv*
        (lambda (cp fv* th)
          (let ([ov* (map var-slot fv*)])
            (fold-left (lambda (i fv) (var-slot-set! fv (cons cp i)) (fx+ i 1)) 0 fv*)
            (let ([v (th)])
              (for-each var-slot-set! fv* ov*)
              v)))))
    (var : var (x) -> Expr ()
      (cond
        [(var-slot x) => (lambda (pr) `(,procedure-ref-pr ,(car pr) (quote ,(cdr pr))))]
        [else x]))
    (Expr : Expr (e) -> Expr ()
      (definitions
        (define (build-procedure-set! x* e** e)
          (let ([ps* (fold-right
                       (lambda (x e* ps*)
                         (fold-right
                           (lambda (e i ps*)
                             (cons `(,procedure-set!-pr ,x (quote ,i) ,e) ps*))
                           ps* e* (enumerate e*)))
                       '() x* e**)])
            (if (null? ps*)
                e
                `(begin ,ps* ... ,e)))))
      [,x 
       (var x)]
      [(letrec ([,l0* ,[f*]] ...)
         (closures ([,x* ,l1* ,[e**] ...] ...) ,[e]))
       `(letrec ([,l0* ,f*] ...)
          (let ([,x* ,(map (lambda (l e*) `(,make-procedure-pr ,l (quote ,(length e*)))) l1* e**)] ...)
            ,(build-procedure-set! x* e** e)))]
      [(,l ,[e*] ...) `(,l ,e* ...)]
      [(,pr ,[e*] ...) `(,pr ,e* ...)]
      [(,[e] ,[e*] ...) `((,procedure-code-pr ,e) ,e* ...)]
      ;; NB: should be unnecessary
      [(letrec ([,l* ,f*] ...) ,clbody) (errorf who "unreachable")])
    (Lambda : Lambda (f) -> Lambda ()
      [(lambda (,x* ...) (bind-free (,x ,x0* ...) ,e))
       (with-fv* x x0* (lambda () `(lambda (,x* ...) ,(Expr e))))]
      ;; NB: should be unnecesary
      [(lambda (,x* ...) ,bfrbody) (error who "unreachable")]))

  (define-language Llifted
    (extends Lproc)
    (entry Program)
    (Program (prog)
      (+ (letrec ([l* f*] ...) e)))
    (Expr (e)
      (- (letrec ([l* f*] ...) e))))

  (define-pass lift-letrec : Lproc (ir) -> Llifted ()
    (definitions
      (define all-l*)
      (define all-f*))
    (Expr : Expr (ir) -> Expr ()
      [(letrec ([,l* ,[f*]] ...) ,[e])
       (set! all-l* (append l* all-l*))
       (set! all-f* (append f* all-f*))
       e])
    (fluid-let ([all-l* '()] [all-f* '()])
      (let ([e (Expr ir)])
        `(letrec ([,all-l* ,all-f*] ...) ,e))))

  (define (value-primitive-info? x)
    (and (primitive-info? x) (eq? (primitive-info-kind x) 'value)))
  (define (effect-primitive-info? x)
    (and (primitive-info? x) (eq? (primitive-info-kind x) 'effect)))
  (define (predicate-primitive-info? x)
    (and (primitive-info? x) (eq? (primitive-info-kind x) 'predicate)))

  (define-language Lnormalized
    (extends Llifted)
    (terminals
      (- (primitive-info (pr)))
      (+ (value-primitive-info (value-pr))    => primitive-info-name
         (predicate-primitive-info (pred-pr)) => primitive-info-name
         (effect-primitive-info (effect-pr))  => primitive-info-name))
    (Program (prog)
      (- (letrec ([l* f*] ...) e))
      (+ (letrec ([l* f*] ...) v)))
    (Lambda (f)
      (- (lambda (x* ...) e))
      (+ (lambda (x* ...) v)))
    (Expr (e)
      (- l
         x
         (quote i)
         (if e0 e1 e2)
         (begin e* ... e)
         (let ([x* e*] ...) e)
         (callable e* ...)))
    (Callable (callable)
      (- e
         pr))
    (Value (v)
      (+ l
         x
         (quote i)
         (if pr0 v1 v2)
         (begin ef* ... v)
         (let ([x* v*] ...) v)
         (vcallable v* ...)))
    (ValueCallable (vcallable)
      (+ v
         value-pr))
    (Pred (pr)
      (+ (true)
         (false)
         (if pr0 pr1 pr2)
         (begin ef* ... pr)
         (let ([x* v*] ...) pr)
         (pred-pr v* ...)))
    (Effect (ef)
      (+ (nop)
         (if pr0 ef1 ef2)
         (begin ef* ... ef)
         (let ([x* v*] ...) ef)
         (ecallable v* ...)))
    (EffectCallable (ecallable)
      (+ v
         effect-pr)))

  (define eq?-pr (primitive->primitive-info 'eq?))

  (define-pass normalize-context : Llifted (ir) -> Lnormalized ()
    (Value : Expr (ir) -> Value ()
      [(,pr ,[v*] ...)
       (cond
         [(value-primitive-info? pr) `(,pr ,v* ...)]
         [(predicate-primitive-info? pr) `(if (,pr ,v* ...) (quote #t) (quote #f))]
         [(effect-primitive-info? pr) `(begin (,pr ,v* ...) (,void-pr))])])
    (Pred : Expr (ir) -> Pred ()
      [,l `(true)]
      [,x `(if (,eq?-pr ,x (quote #f)) (false) (true))]
      [(quote ,i) (if (eq? i #f) `(false) `(true))]
      [(,pr ,[v*] ...)
       (cond
         [(value-primitive-info? pr) `(if (,eq?-pr (,pr ,v* ...) (quote #f)) (false) (true))]
         [(predicate-primitive-info? pr) `(,pr ,v* ...)]
         [(effect-primitive-info? pr) `(begin (,pr ,v* ...) (true))])]
      [(,[v] ,[v*] ...) `(if (,eq?-pr (,v ,v* ...) (quote #f)) (false) (true))])
    (Effect : Expr (ir) -> Effect ()
      [,l `(nop)]
      [,x `(nop)]
      [(quote ,i) `(nop)]
      [(,pr ,[v*] ...) (guard (effect-primitive-info? pr)) `(,pr ,v* ...)]
      [(,pr ,[ef*] ...)
       (let ([ef* (remp (lambda (ef) (nanopass-case (Lnormalized Effect) ef [(nop) #t] [else #f])) ef*)])
         (cond
           [(null? ef*) `(nop)]
           [(= (length ef*) 1) (car ef*)]
           [else (let loop ([ef (car ef*)] [ef* (cdr ef*)] [ref* '()])
                   (if (null? ef*)
                       `(begin ,(reverse ref*) ... ,ef)
                       (loop (car ef*) (cdr ef*) (cons ef ref*))))]))]))

  (define (binary-operator? x) (memq x '(+ - * sra logand)))
  (define (relational-operator? x) (memq x '(< <= = >= > !=)))

  (define-language Lrep
    (extends Lnormalized)
    (terminals
      (- (immediate (i))
         (value-primitive-info (value-pr))
         (predicate-primitive-info (pred-pr))
         (effect-primitive-info (effect-pr)))
      (+ (exact-integer (int))
         (relational-operator (relop))
         (binary-operator (binop))))
    (Triv (tr)
      (+ x
         int
         l))
    (Value (v)
      (- l
         x
         (quote i)
         (vcallable v* ...))
      (+ tr
         (alloc v)
         (mref v0 v1)
         (binop v0 v1)
         (call v v* ...) => (v v* ...)))
    (ValueCallable (vcallable)
      (- v
         value-pr))
    (Pred (pr)
      (- (pred-pr v* ...))
      (+ (relop v0 v1)))
    (Effect (ef)
      (- (ecallable v* ...))
      (+ (mset! v0 v1 v2)
         (call v v* ...) => (v v* ...)))
    (EffectCallable (ecallable)
      (- v
         effect-pr)))

  (define-pass specify-representation : Lnormalized (ir) -> Lrep ()
    (definitions
      (define-syntax with-args
        (syntax-rules ()
          [(_ ([(vs ...) v*]) body0 ... body1)
           (apply
             (case-lambda
               [(vs ...) body0 ... body1]
               [any (errorf who "expected ~s arguments but got ~s" (length '(vs ...)) (length any))])
             v*)])))
    (Value : Value (ir) -> Value ()
      [(quote ,i)
       (cond
         [(eq? i #t) $true]
         [(eq? i #f) $false]
         [(eq? i '()) $nil]
         [else (bitwise-ior (bitwise-arithmetic-shift-left i shift-fixnum) tag-fixnum)])]
      [(,value-pr ,[v*] ...)
       (let ([prim-name (primitive-info-name value-pr)])
         (case prim-name
           [(+ -) (with-args ([(v0 v1) v*]) `(,prim-name ,v0 ,v1))]
           [(*)
            (with-args ([(v0 v1) v*])
              (cond
                [(exact-integer? v0) `(,prim-name ,(bitwise-arithmetic-shift-right v0 shift-fixnum) ,v1)]
                [(exact-integer? v1) `(,prim-name ,v0 ,(bitwise-arithmetic-shift-right v1 shift-fixnum))]
                [else `(,prim-name ,v0 (sra ,v1 ,shift-fixnum))]))]
           [(car) (with-args ([(v0) v*]) `(mref ,v0 ,(- disp-car tag-pair)))]
           [(cdr) (with-args ([(v0) v*]) `(mref ,v0 ,(- disp-cdr tag-pair)))]
           [(cons) (with-args ([(v0 v1) v*])
                     (let ([a (make-var 'a)] [d (make-var 'd)] [t (make-var 'p)])
                       `(let ([,a ,v0] [,d ,v1])
                          (let ([,t (+ (alloc ,size-pair) ,tag-pair)])
                            (begin
                              (mset! ,t ,(- disp-car tag-pair) ,a)
                              (mset! ,t ,(- disp-cdr tag-pair) ,d)
                              ,t)))))]
           [(make-vector)
            (with-args ([(v) v*])
              (let ([t (make-var 'v)])
                (if (exact-integer? v)
                    `(let ([,t (+ (alloc ,(+ disp-vector-data v)) ,tag-vector)])
                       (begin
                         (mset! ,t ,(- disp-vector-length tag-vector) ,v)
                         ,t))
                    (let ([size (make-var 'size)])
                      `(let ([,size ,v])
                         (let ([,t (+ (alloc (+ ,disp-vector-data ,size)) ,tag-vector)])
                           (begin
                             (mset! ,t ,(- disp-vector-length tag-vector) ,size)
                             ,t)))))))]
           [($make-procedure)
            (with-args ([(l size) v*])
              (let ([t (make-var 'proc)])
                (if (exact-integer? size)
                    `(let ([,t (+ (alloc ,(+ disp-procedure-data size)) ,tag-procedure)])
                       (begin
                         (mset! ,t ,(- disp-procedure-code tag-procedure) ,l)
                         ,t))
                    (let ([tsize (make-var 'size)])
                      `(let ([,tsize ,size])
                         (let ([,t (+ (alloc (+ ,disp-procedure-data ,tsize)) ,tag-procedure)])
                           (begin
                             (mset! ,t ,(- disp-procedure-code tag-procedure) ,l)
                             ,t)))))))]
           [($procedure-code) (with-args ([(v) v*]) `(mref ,v ,(- disp-procedure-code tag-procedure)))]
           [($procedure-ref)
            (with-args ([(v0 v1) v*])
              (if (exact-integer? v1)
                  `(mref ,v0 ,(+ (- disp-procedure-data tag-procedure) v1))
                  `(mref ,v0 (+ ,(- disp-procedure-data tag-procedure) ,v1))))]
           [(vector-length) (with-args ([(v) v*]) `(mref ,v ,(- disp-vector-length tag-vector)))]
           [(vector-ref) (with-args ([(v0 v1) v*])
                           (if (exact-integer? v1)
                               `(mref ,v0 ,(+ (- disp-vector-data tag-vector) v1))
                               `(mref ,v0 (+ ,(- disp-vector-data tag-vector) ,v1))))]
           [(void) $void]
           [else (errorf who "unsupported value primitive ~s" prim-name)]))]
      [(,[v] ,[v*] ...) `(call ,v ,v* ...)])
    (Pred : Pred (ir) -> Pred ()
      [(,pred-pr ,[v*] ...)
       (let ([prim-name (primitive-info-name pred-pr)])
         (case prim-name
           [(<) (with-args ([(v0 v1) v*])
                  (if (and (exact-integer? v0) (exact-integer? v1))
                      (if (< v0 v1) `(true) `(false))
                      `(< ,v0 ,v1)))]
           [(<=) (with-args ([(v0 v1) v*])
                   (if (and (exact-integer? v0) (exact-integer? v1))
                       (if (<= v0 v1) `(true) `(false))
                       `(<= ,v0 ,v1)))]
           [(= eq?) (with-args ([(v0 v1) v*])
                      (if (and (exact-integer? v0) (exact-integer? v1))
                          (if (= v0 v1) `(true) `(false))
                          `(= ,v0 ,v1)))]
           [(>=) (with-args ([(v0 v1) v*])
                   (if (and (exact-integer? v0) (exact-integer? v1))
                       (if (>= v0 v1) `(true) `(false))
                       `(>= ,v0 ,v1)))]
           [(>) (with-args ([(v0 v1) v*])
                  (if (and (exact-integer? v0) (exact-integer? v1))
                      (if (> v0 v1) `(true) `(false))
                      `(> ,v0 ,v1)))]
           [(boolean?) (with-args ([(v) v*])
                         (if (exact-integer? v)
                             (if (or (= v $true) (= v $false)) `(true) `(false))
                             `(= (logand ,v ,mask-boolean) ,tag-boolean)))]
           [(fixnum?) (with-args ([(v) v*])
                        (if (exact-integer? v)
                            (if (= (bitwise-and v mask-fixnum) tag-fixnum) `(true) `(false))
                            `(= (logand ,v ,mask-fixnum) ,tag-fixnum)))]
           [(null?) (with-args ([(v) v*])
                      (if (exact-integer? v)
                          (if (= v $nil) `(true) `(false))
                          `(= ,v ,$nil)))]
           [(pair?) (with-args ([(v) v*]) `(= (logand ,v ,mask-pair) ,tag-pair))]
           [(vector?) (with-args ([(v) v*]) `(= (logand ,v ,mask-vector) ,tag-vector))]
           [(procedure?) (with-args ([(v) v*]) `(= (logand ,v ,mask-procedure) ,tag-procedure))]
           [else (errorf who "unsupported predicate primitive ~s" prim-name)]))])
    (Effect : Effect (ir) -> Effect ()
      [(,effect-pr ,[v*] ...)
       (let ([prim-name (primitive-info-name effect-pr)])
         (case prim-name
           [(set-car!) (with-args ([(v0 v1) v*]) `(mset! ,v0 ,(- disp-car tag-pair) ,v1))]
           [(set-cdr!) (with-args ([(v0 v1) v*]) `(mset! ,v0 ,(- disp-cdr tag-pair) ,v1))]
           [($procedure-set!)
            (with-args ([(v0 v1 v2) v*])
              (if (exact-integer? v1)
                  `(mset! ,v0 ,(+ (- disp-procedure-data tag-procedure) v1) ,v2)
                  `(mset! ,v0 (+ ,(- disp-procedure-data tag-procedure) ,v1) ,v2)))]
           [(vector-set!)
            (with-args ([(v0 v1 v2) v*])
              (if (exact-integer? v1)
                  `(mset! ,v0 ,(+ (- disp-vector-data tag-vector) v1) ,v2)
                  `(mset! ,v0 (+ ,(- disp-vector-data tag-vector) ,v1) ,v2)))]
           [else (errorf who "unsupported effect primitive ~s" prim-name)]))]
      [(,[v] ,[v*] ...) `(call ,v ,v* ...)]))

  (define-language Llocals
    (extends Lrep)
    (Program (prog)
      (- (letrec ([l* f*] ...) v))
      (+ (letrec ([l* f*] ...) b)))
    (Lambda (f)
      (- (lambda (x* ...) v))
      (+ (lambda (x* ...) b)))
    (Body (b)
      (+ (locals (x* ...) v))))

  (define-pass uncover-locals : Lrep (ir) -> Llocals ()
    (definitions (define local*))
    (Program : Program (ir) -> Program ()
      [(letrec ([,l* ,[f*]] ...) ,v)
       (fluid-let ([local* '()])
         (let ([v (Value v)])
           `(letrec ([,l* ,f*] ...) (locals (,local* ...) ,v))))])
    (Lambda : Lambda (ir) -> Lambda ()
      [(lambda (,x* ...) ,v)
       (fluid-let ([local*  '()])
         (let ([v (Value v)])
           `(lambda (,x* ...) (locals (,local* ...) ,v))))])
    (Value : Value (ir) -> Value ()
      [(let ([,x* ,[v*]] ...) ,[v])
       (set! local* (append x* local*))
       `(let ([,x* ,v*] ...) ,v)])
    (Pred : Pred (ir) -> Pred ()
      [(let ([,x* ,[v*]] ...) ,[pr])
       (set! local* (append x* local*))
       `(let ([,x* ,v*] ...) ,pr)])
    (Effect : Effect (ir) -> Effect ()
      [(let ([,x* ,[v*]] ...) ,[ef])
       (set! local* (append x* local*))
       `(let ([,x* ,v*] ...) ,ef)]))

  (define-language Lno-let
    (extends Llocals)
    (Value (v)
      (- (let ([x* v*] ...) v)))
    (Pred (pr)
      (- (let ([x* v*] ...) pr)))
    (Effect (ef)
      (- (let ([x* v*] ...) ef))
      (+ (set! x v))))

  (define-pass remove-let : Llocals (ir) -> Lno-let ()
    (definitions
      (define (build-set! x* v*)
        (map (lambda (x v) (with-output-language (Lno-let Effect) `(set! ,x ,v))) x* v*)))
    (Value : Value (ir) -> Value ()
      (definitions
        (define-begin-builder make-begin
          [(Lno-let Effect) (begin ,ef* ... ,ef)]
          [(Lno-let Value) (begin ,ef* ... ,v)]))
      [(let ([,x* ,[v*]] ...) ,[v]) (make-begin (build-set! x* v*) v)])
    (Pred : Pred (ir) -> Pred ()
      (definitions
        (define-begin-builder make-begin
          [(Lno-let Effect) (begin ,ef* ... ,ef)]
          [(Lno-let Pred) (begin ,ef* ... ,pr)]))
      [(let ([,x* ,[v*]] ...) ,[pr]) (make-begin (build-set! x* v*) pr)])
    (Effect : Effect (ir) -> Effect ()
      (definitions
        (define-begin-builder make-begin
          [(Lno-let Effect) (begin ,ef* ... ,ef)]))
      [(let ([,x* ,[v*]] ...) ,[ef]) (make-begin (build-set! x* v*) ef)]))


  (define-language Lsimple-opnd
    (extends Lno-let)
    (Pred (pr)
      (- (relop v0 v1))
      (+ (relop tr0 tr1)))
    (Value (v)
      (- (binop v0 v1)
         (call v v* ...)
         (mref v0 v1)
         (alloc v))
      (+ (binop tr0 tr1)
         (call tr tr* ...)
         (mref tr0 tr1)
         (alloc tr)))
    (Effect (ef)
      (- (call v v* ...)
         (mset! v0 v1 v2))
      (+ (call tr tr* ...)
         (mset! tr0 tr1 tr2))))

  (define-pass remove-complex-opera* : Lno-let (ir) -> Lsimple-opnd ()
    (definitions
      (define local*)
      (define (make-temp)
        (let ([t (make-var 't)])
          (set! local* (cons t local*))
          t))
      (define simplify
        (case-lambda
          [(v k) (Simplify v '() k)]
          [(v0 v1 k)
           (Simplify v0 '()
             (lambda (e* tr0)
               (Simplify v1 e*
                 (lambda (e* tr1)
                   (k e* tr0 tr1)))))]
          [(v0 v1 v2 k)
           (Simplify v0 '()
             (lambda (e* tr0)
               (Simplify v1 e*
                 (lambda (e* tr1)
                   (Simplify v2 e*
                     (lambda (e* tr2)
                       (k e* tr0 tr1 tr2)))))))]))
      (define (simplify* v v* k)
        (Simplify v '()
          (lambda (e* tr)
            (let loop ([v* v*] [e* e*] [rtr* '()])
              (if (null? v*)
                  (k e* tr (reverse rtr*))
                  (Simplify (car v*) e*
                    (lambda (e* tr)
                      (loop (cdr v*) e* (cons tr rtr*))))))))))
    (Body : Body (ir) -> Body ()
      [(locals (,x* ...) ,v)
       (fluid-let ([local* x*])
         (let ([v (Value v)])
           `(locals (,local* ...) ,v)))])
    (Value : Value (ir) -> Value ()
      (definitions
        (define-begin-builder make-begin
          [(Lsimple-opnd Effect) (begin ,ef* ... ,ef)]
          [(Lsimple-opnd Value) (begin ,ef* ... ,v)]))
      [(call ,v ,v* ...)
       (simplify* v v*
         (lambda (e* tr tr*)
           (make-begin e* `(call ,tr ,tr* ...))))]
      [(,binop ,v0 ,v1)
       (simplify v0 v1
         (lambda (e* tr0 tr1)
           (make-begin e* `(,binop ,tr0 ,tr1))))]
      [(alloc ,v)
       (simplify v
         (lambda (e* tr)
           (make-begin e* `(alloc ,tr))))]
      [(mref ,v0 ,v1)
       (simplify v0 v1
         (lambda (e* tr0 tr1)
           (make-begin e* `(mref ,tr0 ,tr1))))])
    (Pred : Pred (ir) -> Pred ()
      (definitions
        (define-begin-builder make-begin
          [(Lsimple-opnd Effect) (begin ,ef* ... ,ef)]
          [(Lsimple-opnd Pred) (begin ,ef* ... ,pr)]))
      [(,relop ,v0 ,v1)
       (simplify v0 v1
         (lambda (e* tr0 tr1)
           (make-begin e* `(,relop ,tr0 ,tr1))))])
    (Effect : Effect (ir) -> Effect ()
      (definitions
        (define-begin-builder make-begin
          [(Lsimple-opnd Effect) (begin ,ef* ... ,ef)]))
      [(call ,v ,v* ...)
       (simplify* v v*
         (lambda (e* tr tr*)
           (make-begin e* `(call ,tr ,tr* ...))))]
      [(mset! ,v0 ,v1 ,v2)
       (simplify v0 v1 v2
         (lambda (e* tr0 tr1 tr2)
           (make-begin e* `(mset! ,tr0 ,tr1 ,tr2))))])
    (Simplify : Value (ir e* k) -> Triv ()
      [,tr (k e* tr)]
      [else (let ([t (make-temp)] [v (Value ir)])
              (k (cons (in-context Effect `(set! ,t ,v)) e*) t))]))

  (define-language Lflat-set!
    (extends Lsimple-opnd)
    (Effect (ef)
      (- (set! x v))
      (+ (set! x rhs)))
    (Rhs (rhs)
      (+ tr
         (alloc tr)
         (mref tr0 tr1)
         (binop tr0 tr1)
         (call tr tr* ...)))
    (Body (b)
      (- (locals (x* ...) v))
      (+ (locals (x* ...) t)))
    (Tail (t)
      (+ tr
         (binop tr0 tr1)
         (alloc tr)
         (mref tr0 tr1)
         (call tr tr* ...)
         (if pr0 t1 t2)
         (begin ef* ... t)))
    (Value (v)
      (- tr
         (binop tr0 tr1)
         (alloc tr)
         (mref tr0 tr1)
         (call tr tr* ...)
         (if pr0 v1 v2)
         (begin ef* ... v))))

  (define-pass flatten-set! : Lsimple-opnd (ir) -> Lflat-set! ()
    (Effect : Effect (ir) -> Effect ()
      [(set! ,x ,v) (Value v x)])
    (Value : Value (ir x) -> Effect ()
      [,tr `(set! ,x ,tr)]
      [(alloc ,tr) `(set! ,x (alloc ,tr))]
      [(mref ,tr0 ,tr1) `(set! ,x (mref ,tr0 ,tr1))]
      [(call ,tr ,tr* ...) `(set! ,x (call ,tr ,tr* ...))]
      [(,binop ,tr0 ,tr1) `(set! ,x (,binop ,tr0 ,tr1))]
      [(if ,[pr0] ,[ef1] ,[ef2]) `(if ,pr0 ,ef1 ,ef2)]
      [(begin ,[ef*] ... ,[ef]) `(begin ,ef* ... ,ef)]))

  (define-language Lbb
    (extends Lflat-set!)
    (Body (b)
      (- (locals (x* ...) t))
      (+ (locals (x* ...) blocks)))
    (Blocks (blocks)
      (+ (labels ([l* t*] ...) l)))
    (Tail (t)
      (- tr
         (binop tr0 tr1)
         (alloc tr)
         (mref tr0 tr1)
         (call tr tr* ...)
         (if pr0 t1 t2))
      (+ (return tr)
         (goto l)
         (if (relop tr0 tr1) (l0) (l1))))
    (Pred (pr)
      (- (true)
         (false)
         (relop tr0 tr1)
         (if pr0 pr1 pr2)
         (begin ef* ... pr)))
    (Effect (ef)
      (- (nop)
         (if pr0 ef1 ef2)
         (begin ef* ... ef)))
    (Rhs (rhs)
      (+ (tail-call tr tr* ...))))

  (define-pass expose-basic-blocks : Lflat-set! (ir) -> Lbb ()
    (definitions
      (define local*)
      (define (make-temp)
        (let ([t (make-var 'retval)])
          (set! local* (cons t local*))
          t))
      (define (Effect* ef* t tl-ef* label* block*)
        (if (null? ef*)
            (values t tl-ef* label* block*)
            (let-values ([(t tl-ef* label* block*) (Effect* (cdr ef*) t tl-ef* label* block*)])
              (Effect (car ef*) t tl-ef* label* block*))))
      (with-output-language Lbb
        (define (make-begin ef* t)
          (if (null? ef*)
              t
              (in-context Tail `(begin ,ef* ... ,t))))
        (define (make-return rhs label* block*)
          (let ([t (make-temp)])
            (values
              (in-context Tail `(return ,t))
              (list (in-context Effect `(set! ,t ,rhs)))
              label*
              block*)))
        (define (build-block sym t ef* label* block*)
          (let ([l (make-local-label sym)])
            (values l (cons l label*) (cons (make-begin ef* t) block*))))))
    (Body : Body (ir) -> Body ()
      [(locals (,x* ...) ,t)
       (fluid-let ([local* x*])
         (let*-values ([(t ef* label* block*) (Tail t '() '())]
                       [(label label* block*) (build-block 'start t ef* label* block*)])
           `(locals (,local* ...) (labels ([,label* ,block*] ...) ,label))))])
    (Tail : Tail (t label* block*) -> Tail (ef* label* block*)
      [,tr (values `(return ,tr) '() label* block*)]
      [(,binop ,tr0 ,tr1)
       (make-return (in-context Rhs `(,binop ,tr0 ,tr1)) label* block*)]
      [(alloc ,tr)
       (make-return (in-context Rhs `(alloc ,tr)) label* block*)]
      [(mref ,tr0 ,tr1)
       (make-return (in-context Rhs `(mref ,tr0 ,tr1)) label* block*)]
      [(call ,tr ,tr* ...)
       (make-return (in-context Rhs `(tail-call ,tr ,tr* ...)) label* block*)]
      [(begin ,ef* ... ,[t tl-ef* label* block*])
       (Effect* ef* t tl-ef* label* block*)]
      [(if ,pr0 ,t1 ,t2)
       (let*-values ([(t1 ef1* label* block*) (Tail t1 label* block*)]
                     [(t2 ef2* label* block*) (Tail t2 label* block*)]
                     [(label1 label* block*) (build-block 'c t1 ef1* label* block*)]
                     [(label2 label* block*) (build-block 'a t2 ef2* label* block*)])
         (Pred pr0 label1 label2 label* block*))])
    (Pred : Pred (ir t-label f-label label* block*) -> Tail (ef* label* block*)
      [(true) (values `(goto ,t-label) '() label* block*)]
      [(false) (values `(goto ,f-label) '() label* block*)]
      [(,relop ,tr0 ,tr1) (values `(if (,relop ,tr0 ,tr1) (,t-label) (,f-label)) '() label* block*)]
      [(begin ,ef* ... ,[t tl-ef* label* block*])
       (Effect* ef* t tl-ef* label* block*)]
      [(if ,pr0 ,pr1 ,pr2)
       (let*-values ([(t1 ef1* label* block*) (Pred pr1 t-label f-label label* block*)]
                     [(t2 ef2* label* block*) (Pred pr2 t-label f-label label* block*)]
                     [(label1 label* block*) (build-block 'c t1 ef1* label* block*)]
                     [(label2 label* block*) (build-block 'a t2 ef2* label* block*)])
         (Pred pr0 label1 label2 label* block*))])
    (Effect : Effect (ir t tl-ef* label* block*) -> Tail (tl-ef* label* block*)
      [(nop) (values t tl-ef* label* block*)]
      [(set! ,x ,[rhs])
       (values t (cons (in-context Effect `(set! ,x ,rhs)) tl-ef*) label* block*)]
      [(mset! ,tr0 ,tr1 ,tr2)
       (values t (cons (in-context Effect `(mset! ,tr0 ,tr1 ,tr2)) tl-ef*) label* block*)]
      [(call ,tr ,tr* ...)
       (values t (cons (in-context Effect `(call ,tr ,tr* ...)) tl-ef*) label* block*)]
      [(begin ,ef* ... ,[t tl-ef* label* block*])
       (Effect* ef* t tl-ef* label* block*)]
      [(if ,pr0 ,ef1 ,ef2)
       (let-values ([(label label* block*) (build-block 'j t tl-ef* label* block*)])
         (let ([t `(goto ,label)])
           (let*-values ([(t1 tl-ef1* label* block*) (Effect ef1 t '() label* block*)]
                         [(t2 tl-ef2* label* block*) (Effect ef2 t '() label* block*)]
                         [(label1 label* block*) (build-block 'c t1 tl-ef1* label* block*)]
                         [(label2 label* block*) (build-block 'a t2 tl-ef2* label* block*)])
             (Pred pr0 label1 label2 label* block*))))]))

  (define optimize-blocks-reorders (make-parameter #t (lambda (x) (and x #t))))

  ;; TODO: eliminate blocks that are just phi functions
  (define-pass optimize-blocks : Lbb (ir) -> Lbb ()
    (definitions
      (define (label->final-target l)
        (let loop ([fl l])
          (cond
            [(label-slot fl) => loop]
            [(eq? fl l) l]
            [else (set! l fl) fl])))
      (define (filter-out-jumps-to-jumps l* t*)
        (for-each
          (lambda (l t)
            (nanopass-case (Lbb Tail) t
              [(goto ,l0) (label-slot-set! l l0)]
              [else (label-slot-set! l #f)]))
          l* t*))
      (define-record-type graph-node
        (nongenerative)
        (fields tail (mutable written?) (mutable jump-to-jump-target))
        (protocol
          (lambda (new)
            (lambda (tail)
              (new tail #f
                (nanopass-case (Lbb Tail) tail
                  [(goto ,l) l]
                  [else #f]))))))
      (define (build-graph! l* t*)
        (for-each (lambda (l t) (label-slot-set! l (make-graph-node t))) l* t*))
      (define (extract-final-target l)
        (let loop ([fl l])
          (cond
            [(let ([node (label-slot fl)]) (and node (graph-node-jump-to-jump-target node))) => loop]
            [else
              (unless (eq? l fl) (graph-node-jump-to-jump-target-set! (label-slot l) fl))
              fl])))
      (define extend-worklist
        (case-lambda
          [(l wl) (if (graph-node-written? (label-slot l)) wl (cons l wl))]
          [(l0 l1 wl) (extend-worklist l0 (extend-worklist l1 wl))]
          [(l . ls) (if (label? l) (extend-worklist l (apply extend-worklist ls)) l)]))
      (define (rewrite-effect* ef* wl)
        (let loop ([ef* ef*] [wl wl] [ref* '()])
          (if (null? ef*)
              (values (reverse ref*) wl)
              (let-values ([(ef wl) (rewrite-effect (car ef*) wl)])
                (loop (cdr ef*) wl (cons ef ref*)))))))
    (Blocks : Blocks (ir) -> Blocks ()
      [(labels ([,l* ,t*] ...) ,l)
       (if (optimize-blocks-reorders)
           (begin
             (build-graph! l* t*)
             (let loop ([wl (list l)] [rl* '()] [rt* '()])
               (if (null? wl)
                   (begin
                     (for-each (lambda (l) (label-slot-set! l #f)) l*)
                     `(labels ([,(reverse rl*) ,(reverse rt*)] ...) ,l))
                   (let ([l (car wl)] [wl (cdr wl)])
                     (let ([node (label-slot l)])
                       (if (graph-node-written? node)
                           (loop wl rl* rt*)
                           (begin
                             (graph-node-written?-set! node #t)
                             (let-values ([(t wl) (rewrite-tail (graph-node-tail node) wl)])
                               (loop wl (cons l rl*) (cons t rt*))))))))))
           (let-values ([(l* t*) (filter-out-jumps-to-jumps l* t*)])
             (let ([t* (map Tail t*)])
               (for-each (lambda (l) (label-slot-set! l #f)) l*)
               `(labels ([,l* ,t*] ...) ,l))))])
    (Tail : Tail (t) -> Tail ()
      [(goto ,l) `(goto ,(label->final-target l))]
      [(if (,relop ,tr0 ,tr1) (,l0) (,l1))
       `(if (,relop ,tr0 ,tr1)
            (,(label->final-target l0))
            (,(label->final-target l1)))])
    (Triv : Triv (tr) -> Triv ()
      [,l (label->final-target l)])
    (rewrite-tail : Tail (t wl) -> Tail (wl)
      [(begin ,ef* ... ,t)
       (let*-values ([(ef* wl) (rewrite-effect* ef* wl)]
                     [(t wl) (rewrite-tail t wl)])
         (values `(begin ,ef* ... ,t) wl))]
      [(goto ,l)
       (let ([l (extract-final-target l)])
         (values `(goto ,l) (extend-worklist l wl)))]
      [(return ,l)
       (let ([l (extract-final-target l)])
         (values `(return ,l) (extend-worklist l wl)))]
      [(return ,tr) (values `(return ,tr) wl)]
      [(if (,relop ,tr0 ,tr1) (,l0) (,l1))
       (let ([l0 (extract-final-target l0)]
             [l1 (extract-final-target l1)])
         (values `(if (,relop ,tr0 ,tr1) (,l0) (,l1)) (extend-worklist l0 l1 wl)))])
    (rewrite-effect : Effect (ef wl) -> Effect (wl)
      [(set! ,x ,l)
       (let ([l (extract-final-target l)])
         (values `(set! ,x ,l) (extend-worklist l wl)))]))

  (define-language Lssa
    (extends Lbb)
    (Rhs (rhs)
      (+ (phi [tr* l*] ...))))

  (define-pass convert-to-ssa : Lbb (ir) -> Lssa ()
    (definitions
      (define-record-type phi
        (nongenerative)
        (fields x (mutable x*) (mutable l*)))
      (define-record-type graph-node
        (nongenerative)
        (fields
          label
          (mutable prev)
          (mutable assignments)
          (mutable phi*)
          (mutable next graph-node-next $graph-node-next-set!)
          ;; tarjan related
          (mutable low-link)
          (mutable on-stack?)
          ;; tarjan/dominator shared
          (mutable index)
          ;; dominator related
          (mutable idom)
          (mutable df))
        (protocol
          (lambda (new)
            (lambda (l)
              (new l '() '() '() '()
                   ;; tarjan related
                   #f #f #f
                   ;; dominator related
                   #f '())))))

      (define tarjan-scc
        (let ()
          (define (scc n scc*)
            (define (tarjan-step n scc* index stack)
              (graph-node-index-set! n index)
              (graph-node-low-link-set! n index)
              (graph-node-on-stack?-set! n #t)
              (let loop ([m* (graph-node-next n)] [scc* scc*] [index 1] [stack (cons n stack)])
                (if (null? m*)
                    (if (fx=? (graph-node-low-link n) (graph-node-index n))
                        (let build-sc ([stack stack] [sc '()])
                          (let ([m (car stack)] [stack (cdr stack)])
                            (graph-node-on-stack?-set! m #f)
                            (if (eq? m n)
                                (values (cons (cons m sc) scc*) index stack)
                                (build-sc stack (cons m sc)))))
                        (values scc* index stack))
                    (let ([m (car m*)])
                      (cond
                        [(graph-node-index m)
                         (when (graph-node-on-stack? m)
                           (graph-node-low-link-set! n (min (graph-node-low-link n) (graph-node-low-link m))))
                         (loop (cdr m*) scc* index stack)]
                        [else (let-values ([(scc* index stack) (tarjan-step m scc* index stack)])
                                (graph-node-low-link-set! n (min (graph-node-low-link n) (graph-node-low-link m)))
                                (loop (cdr m*) scc* index stack))])))))
            (let-values ([(scc* index stack) (tarjan-step n scc* 0 '())])
              scc*))
          (lambda (n*)
            (fold-left
              (lambda (scc* n)
                (if (graph-node-index n)
                    scc*
                    (scc n scc*)))
              '() n*))))

      (define (number-scc! scc)
        (call-with-values
          (lambda ()
            (let f ([scc scc] [i 0])
              (if (null? scc)
                  (values (make-vector i) 0)
                  (let g ([sc (car scc)] [i i])
                    (if (null? sc)
                        (f (cdr scc) i)
                        (let-values ([(v i) (g (cdr sc) (fx+ i 1))])
                          (let ([c (car sc)])
                            (graph-node-index-set! c i)
                            (vector-set! v i c)
                            (values v (fx+ i 1)))))))))
          (lambda (v idx) v)))

      ;; expects vector of topologically "sorted" graph nodes,
      ;; where the strongly connected components are in some 
      ;; arbitrary order, expects internally 
      (define build-dom-tree!
        (let ()
          (define (intersect v n1 n2)
            (let loop ([i1 (graph-node-index n1)] [i2 (graph-node-index n2)])
              (if (fx=? i1 i2)
                  (vector-ref v i1)
                  (loop
                    (let loop ([i1 i1])
                      (if (fx<? i1 i2)
                          (loop (graph-node-index (graph-node-idom (vector-ref v i1))))
                          i1))
                    (let loop ([i2 i2])
                      (if (fx<? i2 i1)
                          (loop (graph-node-index (graph-node-idom (vector-ref v i2))))
                          i2))))))
          (lambda (v)
            (let* ([i (fx- (vector-length v) 1)]
                   [n (vector-ref v i)]) ;; entry node
              (graph-node-idom-set! n n)
              (let fixed-loop ()
                (let node-loop ([i i] [changed? #f])
                  (if (fx=? i 0)
                      (when changed? (fixed-loop))
                      (let* ([i (fx- i 1)]
                             [n (vector-ref v i)]
                             [p* (graph-node-prev n)])
                        (let inner ([new-idom (find graph-node-idom p*)] [p* p*])
                          (if (null? p*)
                              (begin
                                (unless (eq? (graph-node-idom n) new-idom) (graph-node-idom-set! n new-idom))
                                (node-loop i changed?))
                              (let ([p (car p*)])
                                (if (graph-node-idom p)
                                    (inner (intersect v p new-idom) (cdr p*))
                                    (inner new-idom (cdr p*))))))))))))))

      ;; TODO: replace this with more efficient set implementation using node-indexes
      (define (set-cons x ls) (if (memq x ls) ls (cons x ls)))

      (define (build-df! v)
        (vector-for-each
          (lambda (n)
            (when (> (length (graph-node-prev n)) 1)
              (let ([idom (graph-node-idom n)])
                (for-each
                  (lambda (p)
                    (let loop ([p p])
                      (unless (eq? p idom)
                        (graph-node-df-set! p (set-cons n (graph-node-df p)))
                        (loop (graph-node-idom p)))))
                  (graph-node-prev n)))))
          v))

      (define (find-source-label src dest)
        (let loop ([wl (list src)])
          (if (null? wl)
              (errorf 'find-source-label "couldn't find source label")
              (let ([n (car wl)] [wl (cdr wl)])
                (let ([next* (graph-node-next n)])
                  (if (memq dest next*)
                      (graph-node-label n)
                      (loop (append next* wl))))))))

      (define (add-phi! x dest src)
        (let ([src-l (find-source-label src dest)])
          (let ([phi (find (lambda (phi) (eq? x (phi-x phi))) (graph-node-phi* dest))])
            (cond
              [(and phi (memq src-l (phi-l* phi))) (void)]
              [phi 
               (graph-node-assignments-set! dest (cons x (graph-node-assignments dest)))
               (rename-var! x dest)
               (phi-l*-set! phi (cons src-l (phi-l* phi)))
               (phi-x*-set! phi (cons x (phi-x* phi)))]
              [else (graph-node-phi*-set! dest
                      (cons (make-phi x (list x) (list src-l))
                            (graph-node-phi* dest)))]))))

      (define (find-match x as* l)
        (let loop ([node (label-graph-node l)])
          (cond
            [(assq node as*) => cdr]
            [else (let ([prev* (graph-node-prev node)])
                    (when (null? prev*)
                      (errorf 'find-match "unable to find ~s for ~s~%" (var-unique-name x) (label-unique-name l)))
                    (loop (car prev*)))])))

      (define (rename-var! x node)
        (cond
          [(var-slot x) =>
           (lambda (as*)
             (unless (assq node as*)
               (var-slot-set! x (cons (cons node (make-var x)) as*))))]
          [else (var-slot-set! x (list (cons node (make-var x))))]))

      (define (insert-phi! v all-x*)
        (for-each
          (lambda (x)
            #;(printf "x: ~s, multiply-assigned? ~s~%" x (var-flags-multiply-assigned? x))
            (when (var-flags-multiply-assigned? x)
              (let ([wl (let loop ([i (vector-length v)] [wl '()])
                          (if (fx=? i 0)
                              wl
                              (let ([i (fx- i 1)])
                                (loop i (let ([n (vector-ref v i)])
                                          (if (memq x (graph-node-assignments n))
                                              (set-cons n wl)
                                              wl))))))])
                #;(printf "wl: ~s~%" (map (lambda (n) (label-unique-name (graph-node-label n))) wl))
                (let loop ([wl wl] [ever-on-wl wl])
                  (unless (null? wl)
                    (let ([n (car wl)])
                      (rename-var! x n)
                      (let inner ([d* (graph-node-df n)] [wl (cdr wl)] [ever-on-wl ever-on-wl])
                        (if (null? d*)
                            (loop wl ever-on-wl)
                            (let ([d (car d*)])
                              #;(printf "adding phi for ~s to ~s for ~s~%"
                                      (var-unique-name x)
                                      (label-unique-name (graph-node-label d))
                                      (label-unique-name (graph-node-label n)))
                              (add-phi! x d n)
                              (if (memq d ever-on-wl)
                                  (inner (cdr d*) wl ever-on-wl)
                                  (inner (cdr d*) (cons d wl) (cons d ever-on-wl))))))))))))
          all-x*))

      (define (label-graph-node l)
        (or (label-slot l)
            (let ([n (make-graph-node l)])
              (label-slot-set! l n)
              n)))
      (define (graph-node-next-set! n l*)
        (let ([n* (map label-graph-node l*)])
          ($graph-node-next-set! n n*)
          (for-each
            (lambda (nn)
              (graph-node-prev-set! nn (cons n (graph-node-prev nn))))
            n*)))
      (define (label-phi* l)
        (graph-node-phi* (label-graph-node l)))
      )
    (Program : Program (ir) -> Program ()
      [(letrec ([,l* ,[f*]] ...) ,b) `(letrec ([,l* ,f*] ...) ,(Body b '()))])
    (Lambda : Lambda (ir) -> Lambda ()
      [(lambda (,x* ...) ,b) `(lambda (,x* ...) ,(Body b x*))])
    (Body : Body (ir entry-x*) -> Body ()
      [(locals (,x* ...) ,blocks)
       (for-each (lambda (x) (var-flags-assigned-set! x #f) (var-flags-multiply-assigned-set! x #f)) x*)
       (for-each (lambda (x) (var-flags-assigned-set! x #t) (var-flags-multiply-assigned-set! x #f)) entry-x*)
       (let ([blocks (Blocks blocks entry-x* (append x* entry-x*))])
         (for-each (lambda (x) (var-slot-set! x #f)) x*)
         (for-each (lambda (x) (var-slot-set! x #f)) entry-x*)
         `(locals (,x* ...) ,blocks))])
    (Blocks : Blocks (ir entry-x* all-x*) -> Blocks ()
      [(labels ([,l* ,t*] ...) ,l)
       (for-each ScanTail! t* l*) ;; build the graph
       (let* ([artificial-entry-label (make-label 'artifical-entry-node)]
              [artificial-entry-node (label-graph-node artificial-entry-label)])
         (graph-node-next-set! artificial-entry-node (list l))
         (graph-node-assignments-set! artificial-entry-node entry-x*)
         (let* ([scc* (tarjan-scc (cons artificial-entry-node (map label-graph-node l*)))]
                [v (number-scc! scc*)])
           (build-dom-tree! v)
           (build-df! v)
           (insert-phi! v all-x*)
           (let ([t* (map (lambda (t l) (Tail t l #t)) t* l*)])
             (for-each (lambda (l) (label-slot-set! l #f)) l*)
             `(labels ([,l* ,t*] ...) ,l))))])
    (ScanTail! : Tail (t l) -> * (void)
      [(begin ,ef* ... ,[* v]) (for-each (lambda (ef) (ScanEffect! ef l)) ef*)]
      [(goto ,l0) (graph-node-next-set! (label-graph-node l) (list l0))]
      [(if (,relop ,tr0 ,tr1) (,l0) (,l1))
       (graph-node-next-set! (label-graph-node l) (list l0 l1))]
      [(return ,tr) (void)])
    (ScanEffect! : Effect (ef l) -> * (void)
      [(set! ,x ,rhs)
       #;(printf "before in ~s, x: ~s, assigned? ~s, multiply-assigned? ~s~%" (label-unique-name l) (var-unique-name x) (var-flags-assigned? x) (var-flags-multiply-assigned? x))
       (if (var-flags-assigned? x)
           (var-flags-multiply-assigned-set! x #t)
           (var-flags-assigned-set! x #t))
       #;(printf "after in ~s, x: ~s, assigned? ~s, multiply-assigned? ~s~%" (label-unique-name l) (var-unique-name x) (var-flags-assigned? x) (var-flags-multiply-assigned? x))
       (let ([n (label-graph-node l)])
         (graph-node-assignments-set! n
           (cons x (graph-node-assignments n))))]
      [else (void)])
    (Tail : Tail (t l entry?) -> Tail ()
      (definitions
        (define (insert-phi phi* ef* l)
          (fold-left
            (lambda (ef* phi)
              (let ([x (phi-x phi)] [l* (phi-l* phi)])
                (cons 
                  (in-context Effect
                    `(set! ,(var x l) (phi [,(map (lambda (l) (var x l)) l*) ,l*] ...)))
                ef*)))
            ef* phi*))
        (define (maybe-insert-phi entry? l ef* t)
          (let ([ef* (if entry? (insert-phi (label-phi* l) ef* l) ef*)])
            (if (null? ef*)
                t
                `(begin ,ef* ... ,t)))))
      [(begin ,[ef*] ... ,[t l #f -> t])
       (maybe-insert-phi entry? l ef* t)]
      [(goto ,l0)
       (maybe-insert-phi entry? l '() `(goto ,l0))]
      [(if (,relop ,[tr0] ,[tr1]) (,l0) (,l1))
       (maybe-insert-phi entry? l '() `(if (,relop ,tr0 ,tr1) (,l0) (,l1)))]
      [(return ,[tr])
       (maybe-insert-phi entry? l '() `(return ,tr))])
    (Effect : Effect (ef l) -> Effect ()
      [(set! ,x ,[rhs]) `(set! ,(var x l) ,rhs)]
      [(mset! ,[tr0] ,[tr1] ,[tr2]) `(mset! ,tr0 ,tr1 ,tr2)]
      [(call ,[tr] ,[tr*] ...) `(call ,tr ,tr* ...)])
    (Rhs : Rhs (rhs l) -> Rhs ())
    (Triv : Triv (tr l) -> Triv ())
    (var : var (x l) -> var ()
      (cond
        [(var-slot x) => (lambda (as*) (find-match x as* l))]
        [else x])))


  (define-language Lflat-funcs
    (extends Lssa)
    (Program (prog)
      (- (letrec ([l* f*] ...) b))
      (+ (letrec ([l* f*] ...) c* ... c)))
    (Body (b)
      (- (locals (x* ...) blocks)))
    (Blocks (blocks)
      (- (labels ([l* t*] ...) l)))
    (Effect (ef)
      (- (set! x rhs)
         (mset! tr0 tr1 tr2)
         (call tr tr* ...)))
    (Tail (t)
      (- (if (relop tr0 tr1) (l0) (l1))
         (goto l)
         (return tr)
         (begin ef* ... t)))
    (Lambda (f)
      (- (lambda (x* ...) b))
      (+ (lambda (x* ...) c* ... c)))
    (Code (c)
      (+ (label l)
         (set! x rhs)
         (mset! tr0 tr1 tr2)
         (call tr tr* ...)
         (goto l)
         (return tr)
         (if (relop tr0 tr1) (l0) (l1)))))

  (define-pass flatten-functions : Lssa (ir) -> Lflat-funcs ()
    (definitions
      (define (Tail* l* t*)
        (with-output-language (Lflat-funcs Code)
          (fold-left
            (lambda (rc* l t)
              (Tail t (cons `(label ,l) rc*)))
            '() l* t*)))
      (define (Effect* ef* rc*)
        (fold-left
          (lambda (rc* ef) (cons (Effect ef) rc*))
          rc* ef*)))
    (Program : Program (prog) -> Program ()
      [(letrec ([,l* ,[f*]] ...) ,[c c*])
       `(letrec ([,l* ,f*] ...) ,c* ... ,c)])
    (Lambda : Lambda (f) -> Lambda ()
      [(lambda (,x* ...) ,[c c*])
       `(lambda (,x* ...) ,c* ... ,c)])
    (Body : Body (b) -> Code (c*)
      [(locals (,x* ...) ,[c c*]) (values c c*)])
    (Blocks : Blocks (blocks) -> Code (c*)
      [(labels ([,l* ,t*] ...) ,l)
       (let ([rc* (if (eq? l (car l*))
                      (Tail* l* t*)
                      (Tail*
                        (cons (make-local-label 'entry) l*)
                        (cons (with-output-language (Lssa Tail) `(goto ,l)) t*)))])
         (values (car rc*) (reverse (cdr rc*))))])
    (Tail : Tail (t rc*) -> Code () ;; cheating, actually returns Code*
      [(goto ,l) (cons `(goto ,l) rc*)]
      [(return ,tr) (cons `(return ,tr) rc*)]
      [(begin ,ef* ... ,t) (Tail t (Effect* ef* rc*))]
      [(if (,relop ,tr0 ,tr1) (,l0) (,l1))
       (cons `(if (,relop ,tr0 ,tr1) (,l0) (,l1)) rc*)])
    (Effect : Effect (ef) -> Code ()))

  (define-pass eliminate-simple-moves : Lflat-funcs (ir) -> Lflat-funcs ()
    (definitions
      (define (Code* c* c)
        (let loop ([c* c*] [rc* '()])
          (if (null? c*)
              (Code c rc*)
              (loop (cdr c*) (Code (car c*) rc*))))))
    (Program : Program (prog) -> Program ()
      [(letrec ([,l* ,[f*]] ...) ,c* ... ,c)
       (for-each IdentifyMove (cons c c*))
       (let ([rc* (Code* c* c)])
         `(letrec ([,l* ,f*] ...) ,(reverse (cdr rc*)) ... ,(car rc*)))])
    (Lambda : Lambda (ir) -> Lambda ()
      [(lambda (,x* ...) ,c* ... ,c)
       (for-each IdentifyMove (cons c c*))
       (let ([rc* (Code* c* c)])
         `(lambda (,x* ...) ,(reverse (cdr rc*)) ... ,(car rc*)))])
    (IdentifyMove : Code (ir) -> * (void)
      [(set! ,x1 ,x2) (var-slot-set! x1 x2)]
      [(set! ,x1 ,int2) (var-slot-set! x1 int2)]
      [else (void)])
    (Code : Code (c rc*) -> * (rc*) ;; cheating really returning Code*
      [(set! ,x1 ,x2) rc*]
      [(set! ,x1 ,int2) rc*]
      [else (cons (SimpleRewrite c) rc*)])
    (SimpleRewrite : Code (c) -> Code ())
    (Triv : Triv (x) -> Triv ()
      [,x (var x)]
      [,int int]
      [,l l])
    (var : var (x) -> Triv ()
      (let loop ([target-x x])
        (let ([next-target-x (var-slot target-x)])
          (cond
            [(eq? next-target-x #f)
             (unless (eq? target-x x) (var-slot-set! x target-x))
             target-x]
            [(exact-integer? next-target-x)
             (var-slot-set! x next-target-x)
             next-target-x]
            [else (loop next-target-x)])))))

  (define-pass generate-llvm-code : Lflat-funcs (ir) -> * (void)
    (definitions
      (define calling-convention
        (if (use-llvm-10-tailcc) "tailcc" "fastcc"))
      (define (var-printable-name x) (format "%\"~s\"" (var-unique-name x)))
      (define (label-printable-name l)
        (if (local-label? l)
            (format "%~s" (label-unique-name l))
            (format "@\"~s\"" (label-unique-name l))))
      (define (relop-to-llvm relop)
        (case relop
          [(<) 'slt]
          [(<=) 'sle]
          [(=) 'eq]
          [(>=) 'sge]
          [(>) 'sgt]
          [(!=) 'ne]
          [else (errorf who "unexpected relop ~s" relop)]))
      (define (binop-to-llvm binop)
        (case binop
          [(+) 'add]
          [(-) 'sub]
          [(*) 'mul]
          [(sra) 'ashr]
          [(logand) 'and]
          [else (errorf who "unexpected binop ~s" binop)]))
      (define (printable-triv tr)
        (cond
          [(local-label? tr) (format "label ~a" (label-printable-name tr))]
          [(label? tr)
           (format "ptrtoint (i64 (~{i64~*~^, ~})* ~a to i64)"
             (label-slot tr) (label-printable-name tr))]
          [(var? tr) (var-printable-name tr)]
          [else (format "~s" tr)]))
      (define (emit-llvm-prelogue)
        (printf "source_filename = \"scheme\"~%")
        (printf "target datalayout = \"e-m:o-i64:64-f80:128-n8:16:32:64-S128\"~%")
        (printf "target triple = \"x86_64-apple-macosx10.15.0\"~%")
        (printf "~%")
        (printf "@.str.nil = private unnamed_addr constant [3 x i8] c\"()\\00\", align 1~%")
        (printf "@.str.hash_t = private unnamed_addr constant [3 x i8] c\"#t\\00\", align 1~%")
        (printf "@.str.hash_f = private unnamed_addr constant [3 x i8] c\"#f\\00\", align 1~%")
        (printf "@.str.void = private unnamed_addr constant [8 x i8] c\"#(void)\\00\", align 1~%")
        (printf "@.str.proc = private unnamed_addr constant [13 x i8] c\"#(procedure)\\00\", align 1~%")
        (printf "@.str.fixnum = private unnamed_addr constant [5 x i8] c\"%lld\\00\", align 1~%")
        (printf "@.str.vector_start = private unnamed_addr constant [3 x i8] c\"#(\\00\", align 1~%")
        (printf "@.str.space = private unnamed_addr constant [2 x i8] c\" \\00\", align 1~%")
        (printf "@.str.close_paren = private unnamed_addr constant [2 x i8] c\")\\00\", align 1~%")
        (printf "@.str.open_paren = private unnamed_addr constant [2 x i8] c\"(\\00\", align 1~%")
        (printf "@.str.dot = private unnamed_addr constant [4 x i8] c\" . \\00\", align 1~%")
        (printf "@.str.unknown = private unnamed_addr constant [11 x i8] c\"#(unknown)\\00\", align 1~%")
        (printf "@.str.newline = private unnamed_addr constant [2 x i8] c\"\\0A\\00\", align 1~%")
        (printf "~%")
        (printf "define void @scheme_write(i64 %val) {~%")
        (printf "entry:~%")
        (printf "  %is_null = icmp eq i64 %val, ~s ; null?~%" $nil)
        (printf "  br i1 %is_null, label %nil, label %not_nil~%")
        (printf "nil:~%")
        (printf "  call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.nil, i32 0, i32 0))~%")
        (printf "  br label %exit~%")
        (printf "not_nil:~%")
        (printf "  %is_true = icmp eq i64 %val, ~s ; true?~%" $true)
        (printf "  br i1 %is_true, label %hash_t, label %not_hash_t~%")
        (printf "hash_t:~%")
        (printf "  call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.hash_t, i32 0, i32 0))~%")
        (printf "  br label %exit~%")
        (printf "not_hash_t:~%")
        (printf "  %is_false = icmp eq i64 %val, ~s ; false?~%" $false)
        (printf "  br i1 %is_false, label %hash_f, label %not_hash_f~%")
        (printf "hash_f:~%")
        (printf "  call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.hash_f, i32 0, i32 0))~%")
        (printf "  br label %exit~%")
        (printf "not_hash_f:~%")
        (printf "  %is_void = icmp eq i64 %val, ~s ; void?~%" $void)
        (printf "  br i1 %is_void, label %undef_val, label %not_undef_val~%")
        (printf "undef_val:~%")
        (printf "  call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([8 x i8], [8 x i8]* @.str.void, i32 0, i32 0))~%")
        (printf "  br label %exit~%")
        (printf "not_undef_val:~%")
        (printf "  %val_proc_masked = and i64 %val, ~s ; mask with procedure mask~%" mask-procedure)
        (printf "  %is_proc = icmp eq i64 %val_proc_masked, ~s ; procedure type?~%" tag-procedure)
        (printf "  br i1 %is_proc, label %procedure, label %not_procedure~%")
        (printf "procedure:~%")
        (printf "  call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([13 x i8], [13 x i8]* @.str.proc, i32 0, i32 0))~%")
        (printf "  br label %exit~%")
        (printf "not_procedure:~%")
        (printf "  %val_fixnum_masked = and i64 %val, ~s ; mask with fixnum mask~%" mask-fixnum)
        (printf "  %is_fixnum = icmp eq i64 %val_fixnum_masked, ~s ; fixnum type?~%" tag-fixnum)
        (printf "  br i1 %is_fixnum, label %fixnum, label %not_fixnum~%")
        (printf "fixnum:~%")
        (printf "  %unfixed = ashr i64 %val, ~s ; fixnum shift~%" shift-fixnum)
        (printf "  call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @.str.fixnum, i32 0, i32 0), i64 %unfixed)~%")
        (printf "  br label %exit~%")
        (printf "not_fixnum:~%")
        (printf "  %val_vector_masked = and i64 %val, ~s ; mask with vector mask~%" mask-vector)
        (printf "  %is_vector = icmp eq i64 %val_vector_masked, ~s ; vector tag~%" tag-vector)
        (printf "  br i1 %is_vector, label %vector, label %not_vector~%")
        (printf "vector:~%")
        (printf "  call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.vector_start, i32 0, i32 0))~%")
        (printf "  %vec_len_addr = add i64 %val, ~s ; pointer to vector-length~%" (- disp-vector-length tag-vector))
        (printf "  %vec_len_ptr = inttoptr i64 %vec_len_addr to i64*~%")
        (printf "  %vec_len = load i64, i64* %vec_len_ptr, align 8 ; vector-length~%")
        (printf "  %vec_data_addr = add i64 %val, ~s ; pointr to vector-data tart~%" (- disp-vector-data tag-vector))
        (printf "  br label %vector_loop~%")
        (printf "vector_loop:~%")
        (printf "  %vec_len.2 = phi i64 [ %vec_len, %vector ], [ %vec_len.3, %vector_cont ]~%")
        (printf "  %vec_data_addr.2 = phi i64 [ %vec_data_addr, %vector ], [ %vec_data_addr.3, %vector_cont ]~%")
        (printf "  %vec_data_ptr = inttoptr i64 %vec_data_addr.2 to i64*~%")
        (printf "  %vec_data = load i64, i64* %vec_data_ptr, align 8 ; vector data~%")
        (printf "  call void @scheme_write(i64 %vec_data)~%")
        (printf "  %vec_len.3 = sub i64 %vec_len.2, ~s~%" word-size)
        (printf "  %vec_data_addr.3 = add i64 %vec_data_addr.2, ~s~%" word-size)
        (printf "  %is_vec_end = icmp eq i64 %vec_len.3, 0~%")
        (printf "  br i1 %is_vec_end, label %vector_end, label %vector_cont~%")
        (printf "vector_cont:~%")
        (printf "  call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.space, i32 0, i32 0))~%")
        (printf "  br label %vector_loop~%")
        (printf "vector_end:~%")
        (printf "  call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.close_paren, i32 0, i32 0))~%")
        (printf "  br label %exit~%")
        (printf "not_vector:~%")
        (printf "  %val_pair_masked = and i64 %val, ~s ; pair mask~%" mask-pair)
        (printf "  %is_pair = icmp eq i64 %val_pair_masked, ~s ; tag pair~%" tag-pair)
        (printf "  br i1 %is_pair, label %pair, label %not_pair~%")
        (printf "pair:~%")
        (printf "  call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.open_paren, i32 0, i32 0))~%")
        (printf "  br label %list_loop~%")
        (printf "list_loop:~%")
        (printf "  %pr = phi i64 [%val, %pair], [%cdr_val, %list_really_cont]~%")
        (printf "  %car_addr = add i64 %pr, ~s ; car disp~%" (- disp-car tag-pair))
        (printf "  %car_ptr = inttoptr i64 %car_addr to i64*~%")
        (printf "  %car_val = load i64, i64* %car_ptr, align 8 ; car~%")
        (printf "  call void @scheme_write(i64 %car_val)~%")
        (printf "  %cdr_addr = add i64 %pr, ~s ; cdr disp~%" (- disp-cdr tag-pair))
        (printf "  %cdr_ptr = inttoptr i64 %cdr_addr to i64*~%")
        (printf "  %cdr_val = load i64, i64* %cdr_ptr, align 8 ; cdr~%")
        (printf "  %cdr_val_is_null = icmp eq i64 %cdr_val, ~s ; null?~%" $nil)
        (printf "  br i1 %cdr_val_is_null, label %list_end, label %list_cont~%")
        (printf "list_end:~%")
        (printf "  call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.close_paren, i32 0, i32 0))~%")
        (printf "  br label %exit~%")
        (printf "list_cont:~%")
        (printf "  %cdr_val_pair_masked = and i64 %cdr_val, ~s ; mask pair~%" mask-pair)
        (printf "  %cdr_val_is_pair = icmp eq i64 %cdr_val_pair_masked, ~s ; tag pair~%" tag-pair)
        (printf "  br i1 %cdr_val_is_pair, label %list_really_cont, label %list_improper_end~%")
        (printf "list_really_cont:~%")
        (printf "  call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.space, i32 0, i32 0))~%")
        (printf "  br label %list_loop~%")
        (printf "list_improper_end:~%")
        (printf "  call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str.dot, i32 0, i32 0))~%")
        (printf "  call void @scheme_write(i64 %cdr_val)~%")
        (printf "  call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.close_paren, i32 0, i32 0))~%")
        (printf "  br label %exit~%")
        (printf "not_pair:~%")
        (printf "  call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([11 x i8], [11 x i8]* @.str.unknown, i32 0, i32 0))~%")
        (printf "  br label %exit~%")
        (printf "exit:~%")
        (printf "  ret void~%")
        (printf "}~%")
        (printf "~%")
        (printf "declare i32 @printf(i8*, ...)~%")
        (printf "declare i8* @malloc(i64)~%")
        (printf "~%"))
      (define (emit-main-function l)
        (printf "define i32 @main(i32, i8**) {~%")
        (printf "  %result = call ~a i64 ~a()~%" calling-convention (label-printable-name l))
        (printf "  call void @scheme_write(i64 %result)~%")
        (printf "  call i32 (i8*, ...) @printf(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str.newline, i32 0, i32 0))~%")
        (printf "  ret i32 0~%")
        (printf "}~%"))
      (define (emit-llvm-prologue)
        (void))
      )
    (Program : Program (prog) -> * (void)
      [(letrec ([,l* ,f*] ...) ,c* ... ,c)
       (for-each LambdaArgs f* l*)
       (emit-llvm-prelogue)
       (for-each Lambda f* l*)
       (let ([entry (make-label 'scheme-entry)])
         (Lambda
           (with-output-language (Lflat-funcs Lambda)
             `(lambda () ,c* ... ,c))
           entry)
         (emit-main-function entry))
       (emit-llvm-prologue)])
    (LambdaArgs : Lambda (f l) -> * (void)
      [(lambda (,x* ...) ,c* ... ,c) (label-slot-set! l x*)])
    (Lambda : Lambda (f l) -> * (void)
      [(lambda (,x* ...) ,c* ... ,c)
       (printf "define ~a i64 ~a(~{i64 ~a~^, ~}) {~%" calling-convention (label-printable-name l) (map var-printable-name x*))
       (fold-left (lambda (i x) (var-slot-set! x i) (fx+ i 1)) 0 x*)
       (for-each Code c*)
       (Code c)
       (printf "}~%")])
    (Code : Code (c) -> * (void)
      [(label ,l)
       (printf "~s:~%" (label-unique-name l))]
      [(set! ,x ,rhs) (Rhs rhs x)]
      [(mset! ,tr0 ,tr1 ,tr2)
       (let ([untagged (make-var 'untagged)]
             [ptr (make-var 'ptr)])
         (printf "  ~a = add i64 ~a, ~a~%" (var-printable-name untagged) (printable-triv tr0) (printable-triv tr1))
         (printf "  ~a = inttoptr i64 ~a to i64*~%" (var-printable-name ptr) (var-printable-name untagged))
         (printf "  store i64 ~a, i64* ~a, align 8~%" (printable-triv tr2) (var-printable-name ptr)))]
      [(call ,l ,tr* ...)
       (printf "  call ~a i64 ~a(~{i64 ~a~^, ~})~%" calling-convention (label-printable-name l) (map printable-triv tr*))]
      [(call ,tr ,tr* ...)
       (let ([fptr (make-var 'fptr)])
         (printf "  ~a = inttoptr i64 ~a to i64 (~{i64~*~^, ~})*~%" (var-printable-name fptr) (printable-triv tr) tr*)
         (printf "  call ~a i64 ~a(~{i64 ~a~^, ~})~%" calling-convention (var-printable-name fptr) (map printable-triv tr*)))]
      [(goto ,l) (printf "  br label ~a~%" (label-printable-name l))]
      [(return ,tr) (printf "  ret i64 ~a~%" (printable-triv tr))]
      [(if (,relop ,tr0 ,tr1) (,l0) (,l1))
       (let ([cmp (make-var 'cmp)])
         (printf "  ~a = icmp ~a i64 ~a, ~a~%" (var-printable-name cmp) (relop-to-llvm relop) (printable-triv tr0) (printable-triv tr1))
         (printf "  br i1 ~a, label ~a, label ~a~%" (var-printable-name cmp) (label-printable-name l0) (label-printable-name l1)))])
    (Rhs : Rhs (rhs x) -> * (void)
      [(phi (,tr* ,l*) ...)
       (printf "  ~a = phi i64 ~{[~{~a~^, ~}]~^, ~}~%" (var-printable-name x) (map list (map printable-triv tr*) (map label-printable-name l*)))]
      [,tr
       (printf "  ~a = ~a~%" (var-printable-name x) (printable-triv tr))]
      [(alloc ,tr)
       (let ([ptr (make-var 'ptr)])
         (printf "  ~a = call i8* @malloc(i64 ~a)~%" (var-printable-name ptr) (printable-triv tr))
         (printf "  ~a = ptrtoint i8* ~a to i64~%" (var-printable-name x) (var-printable-name ptr)))]
      [(mref ,tr0 ,tr1)
       (let ([untagged (make-var 'untagged)]
             [ptr (make-var 'ptr)])
         (printf "  ~a = add i64 ~a, ~a~%" (var-printable-name untagged) (printable-triv tr0) (printable-triv tr1))
         (printf "  ~a = inttoptr i64 ~a to i64*~%" (var-printable-name ptr) (var-printable-name untagged))
         (printf "  ~a = load i64, i64* ~a, align 8~%" (var-printable-name x) (var-printable-name ptr)))]
      [(,binop ,tr0 ,tr1)
       (printf "  ~a = ~a i64 ~a, ~a~%" (var-printable-name x) (binop-to-llvm binop) (printable-triv tr0) (printable-triv tr1))]
      [(tail-call ,l ,tr* ...)
       (printf "  ~a = tail call ~a i64 ~a(~{i64 ~a~^, ~})~%" (var-printable-name x) calling-convention (label-printable-name l) (map printable-triv tr*))]
      [(tail-call ,tr ,tr* ...)
       (let ([fptr (make-var 'fptr)])
         (printf "  ~a = inttoptr i64 ~a to i64 (~{i64~*~^, ~})*~%" (var-printable-name fptr) (printable-triv tr) tr*)
         (printf "  ~a = tail call ~a i64 ~a(~{i64 ~a~^, ~})~%" (var-printable-name x) calling-convention (var-printable-name fptr) (map printable-triv tr*)))]
      [(call ,l ,tr* ...)
       (printf "  ~a = call ~a i64 ~a(~{i64 ~a~^, ~})~%" (var-printable-name x) calling-convention (label-printable-name l) (map printable-triv tr*))]
      [(call ,tr ,tr* ...)
       (let ([fptr (make-var 'fptr)])
         (printf "  ~a = inttoptr i64 ~a to i64 (~{i64~*~^, ~})*~%" (var-printable-name fptr) (printable-triv tr) tr*)
         (printf "  ~a = call ~a i64 ~a(~{i64 ~a~^, ~})~%" (var-printable-name x) calling-convention (var-printable-name fptr) (map printable-triv tr*)))])
    (Program ir))

  (define (rewrite-result x)
    (cond
      [(equal? x '#(void)) (void)]
      [(equal? x '#(procedure)) (lambda () (void))]
      [(pair? x) (cons (rewrite-result (car x)) (rewrite-result (cdr x)))]
      [(vector? x) (vector-map rewrite-result x)]
      [else x]))

  (define-syntax define-compiler
    (lambda (x)
      (syntax-case x ()
        [(_ name (pass ... last-pass))
         (with-implicit (name all-passes)
           #'(begin
               (define all-passes '(pass ... last-pass))
               (define name
                 (lambda (x)
                   (let* ([x (let ([x (pass x)])
                               (when (memq 'pass (traced-passes))
                                 (printf "~s output:~%" 'pass)
                                 (pretty-print ((pass-output-unparser pass) x)))
                               x)]
                          ...)
                     (let-values ([(op p) (open-string-output-port)])
                       (parameterize ([current-output-port op]) (last-pass x))
                       (let ([str (p)])
                         (with-output-to-file "t.ll" (lambda () (display str)) 'replace)
                         (when (memq 'last-pass (traced-passes))
                           (printf "~s output:~%" 'last-pass)
                           (display str))
                         (system (format "clang -O3 -o t t.ll"))
                         (when (file-exists? "t.out") (delete-file "t.out"))
                         (when (file-exists? "t.err") (delete-file "t.err"))
                         (system "./t > t.out 2> t.err")
                         (rewrite-result (call-with-input-file "t.out" read)))))))))])))

  (define-compiler tiny-compile
    (parse-scheme
     convert-complex-datum
     uncover-assigned!
     purify-letrec
     convert-assignments
     optimize-direct-call
     remove-anonymous-lambda
     sanitize-binding-forms
     uncover-free
     convert-closures
     optimize-known-call
     introduce-procedure-primitives
     lift-letrec
     normalize-context
     specify-representation
     uncover-locals
     remove-let
     remove-complex-opera*
     flatten-set!
     expose-basic-blocks
     optimize-blocks
     convert-to-ssa
     flatten-functions
     eliminate-simple-moves
     generate-llvm-code
     ))

  (define traced-passes
    (let ([passes '()])
      (case-lambda
        [() passes]
        [(x) (cond
               [(or (eq? x #f) (null? x)) (set! passes '())]
               [(eq? x #t) (set! passes all-passes)]
               [(symbol? x)
                (cond
                  [(memq x passes) (set! passes (remq x passes))] ;; remove it if it is there
                  [(memq x all-passes) (set! passes (cons x passes))] ;; add it if it is valid
                  [else (errorf 'traced-passes "unrecognized pass ~s" x)])]
               [(and (list? x) (for-all symbol? x))
                (unless (null? (filter (lambda (x) (memq x all-passes)) x)) (errorf 'traced-passes "~s are not passes" (filter (lambda (x) (memq x all-passes)) x)))
                (for-each traced-passes x)]
               [else (errorf 'traced-passes "expected boolean, symbol, or list, but got ~s" x)])])))

  (define tests
    '(7
      '()
      #f
      '(1 2 3 4)
      '#(5 4 3 2 1)
      '#((1 2) (3 4))
      '(#(1 2) #(3 4))
      '(#(#t #f 1) #(#f #t 2))
      (or 10 #f)
      (and #t 45 7)
      (+ 4 5)
      (- 1 4)
      (* 7 9)
      (cons 1 '())
      (car '(1 2))
      (cdr '(1 2))
      (if #t 1 2)
      (pair? '(1 2))
      (pair? '())
      (vector? '#(1 2))
      (vector? '(1 2))
      (boolean? #f)
      (boolean? 7)
      (null? '())
      (null? '(1 2))
      (fixnum? 1234)
      (fixnum? '())
      (procedure? (lambda (x) x))
      (procedure? 7)
      (<= 1 8)
      (<= 8 1)
      (<= 1 1)
      (< 8 1)
      (< 1 8)
      (= 1 1)
      (= 1 0)
      (>= 8 1)
      (>= 1 8)
      (>= 1 1)
      (> 8 1)
      (> 1 8)
      (not #f)
      (not 10)
      ;; value primitives in effect context
      (let ([x 5]) (* 3 x) x)
      (let ([x 5]) (+ 3 x) x)
      (let ([x 5]) (- 3 x) x)
      (let ([x (cons 1 5)]) (car x) x)
      (let ([x (cons 1 5)]) (cdr x) x)
      (let ([x 1] [y 5]) (cons x y) x)
      (begin (make-vector 5) 7)
      (let ([v (make-vector 2)]) (vector-length v) 7)
      (let ([v (make-vector 2)]) (vector-ref v 0) 7)
      (begin (void) 5)
      ;; value primitives in pred
      (if (+ 3 5) '7 8)
      (if (not (* 3 5)) '7 8)
      (if (- 3 5) '7 8)
      (if (cons 3 5) 7 8)
      (if (car (cons #t #f)) 7 8)
      (if (cdr (cons #t #f)) 7 8)
      (if (make-vector 10) 7 8)
      (let ([v (make-vector 10)]) (if (vector-length v) 7 8))
      (let ([v (make-vector 10)])
        (vector-set! v 0 #t)
        (if (vector-ref v 0) 7 8))
      (if (void) 7 8)
      ;; pred prims in value
      (< 7 8)
      (let () (<= 7 8))
      (= 7 8)
      (letrec () (>= 7 8))
      (> 7 8)
      (let () (boolean? #f))
      (not #t)
      (let ([x (cons 1 '())] [y (cons 1 '())]) (eq? x y))
      (fixnum? 7)
      (null? '())
      (letrec () (pair? (cons 1 '())))
      (vector? (make-vector 1))
      (or 5 7 #f 10 11)
      (and #t #t 10 100)
      ;; pred prims in effect
      (letrec () (begin (< 7 8) 7))
      (begin (<= '7 '8) '7)
      (letrec () (= 7 8) 7)
      (begin (>= 7 8) 7)
      (letrec () (begin (> 7 8) 8))
      (letrec () (boolean? #f) 9)
      (letrec () 
        (let ([x (cons 1 '())] [y (cons 1 '())])
          (begin (eq? x y) 10)))
      (letrec () (begin (fixnum? 7) 10))
      (let () (null? '()) 15)
      (letrec () (pair? (cons 1 '())) 20)
      (let () (begin (vector? (make-vector '1)) '10))
      ;; effect prims in value
      (letrec () (set-car! (cons 1 2) 10))
      (let () (set-cdr! (cons 1 2) 14))
      (vector-set! (make-vector 4) 0 10)
      ;; effect prims in pred
      (if (set-car! (cons 1 2) 10) 7 8)
      (letrec () (if (set-cdr! (cons 1 2) 14) 9 10))
      (letrec () (if (vector-set! (make-vector 4) 0 10) 11 12))
  
      (let ([x '(1 2)]) (eq? x x))
      (let ([x '(1 2)] [y '(1 2)]) (eq? x y))
      (+ (let ([x 7] [y 2])
           (if (if (= x 7) (< y 0) (<= 0 y)) 77 88))
         99)
      (if (= (+ 7 (* 2 4)) (- 20 (+ (+ 1 1) (+ (+ 1 1) 1))))
          (+ 1 (+ 1 (+ 1 (+ 1 (+ 1 10)))))
          0)
      (let ([v (make-vector 3)])
        (vector-set! v 0 1)
        (vector-set! v 1 2)
        (vector-set! v 2 3)
        v)
      (cons (let ([f (lambda (h v) (* h v))])
              (let ([k (lambda (x) (+ x 5))])
                (letrec ([x 15])
                  (letrec ([g (lambda (x) (+ 1 x))])
                    (k (g (let ([g 3]) (f g x))))))))
            '())
      (let ([n 4])
        (let ([v (make-vector n)])
          (letrec ([iota-fill! (lambda (v i n)
                                 (if (< i n)
                                     (begin
                                       (vector-set! v i i)
                                       (iota-fill! v (+ i 1) n))))])
            (iota-fill! v 0 n)
            v)))
      (let ([x (cons '1 '())])
        (let ([x (cons '2 x)])
          (let ([x (cons '3 x)])
            (let ([x (cons '4 x)])
              (let ([x (cons '5 x)])
                x)))))
      (let ([n 5])
        (let ([a 1])
          (let ([a (* a n)])
            (let ([n (- n 1)])
              (let ([a (* a n)])
                (let ([n (- n 1)])
                  (let ([a (* a n)])
                    (let ([n (- n 1)])
                      (let ([a (* a n)])
                        a)))))))))
      (let ((n 17) (s 18) (t 19))
        (let ((st (make-vector 5)))
          (vector-set! st 0 n)
          (vector-set! st 1 s)
          (vector-set! st 2 t)
          (if (not (vector? st)) 10000 (vector-length st))))
      (letrec ([list4 (lambda (a b c d) (cons a (cons b (cons c (cons d '())))))])
        (let ([pair '(1 . 2)] [vect (make-vector 3)])
          (list4 (set-car! pair 7) (set-cdr! pair 10) (vector-set! vect 0 16) '())))
      (letrec ([f (lambda (p)
                      (- (vector-ref
                           (vector-ref (vector-ref (vector-ref (vector-ref p 0) 0) 1) 0)
                           (vector-ref (vector-ref p 1) (vector-ref (vector-ref p 0) 4)))
                         (vector-ref
                           (vector-ref p (vector-ref p 2))
                           (vector-ref (vector-ref p 0) (vector-ref p 4)))))]
               [x (make-vector 6)]
               [y (make-vector 7)])
          (begin
            (vector-set! x 0 y)
            (vector-set! x 1 x)
            (vector-set! y 0 x)
            (vector-set! y '1 '-4421)
            (vector-set! x '2 '0)
            (vector-set! x '3 '-37131)
            (vector-set! x '4 '4)
            (vector-set! x '5 '6)
            (vector-set! y '2 '-55151)
            (vector-set! y '3 '-32000911)
            (vector-set! y '4 '5)
            (vector-set! y '5 '55)
            (vector-set! y '6 '-36)
            (* (f x) 2)))
      (let ([vect (make-vector 5)])
        (vector-set! vect 0 123)
        (vector-set! vect 1 10)
        (vector-set! vect 2 7)
        (vector-set! vect 3 12)
        (vector-set! vect 4 57)
        (letrec ([vector-scale! 
                   (lambda (vect scale)
                     (let ([size (vector-length vect)])
                       (letrec ([f (lambda (idx)
                                     (if (>= idx 1)
                                       (let ([idx (- idx 1)])
                                         (vector-set! vect idx
                                                      (* (vector-ref vect idx)
                                                         scale))
                                         (f idx))))])
                         (f size))))])
          (vector-scale! vect 10))
          (letrec ([vector-sum (lambda (vect)
                                 (letrec ([f (lambda (idx)
                                               (if (< idx 1)
                                                   0
                                                   (+ (vector-ref vect (- idx 1))
                                                      (f (- idx 1)))))])
                                   (f (vector-length vect))))])
            (vector-sum vect)))
      (letrec ([a (lambda (u v w x) 
                    (if (= u 0) 
                        (b v w x)
                        (a (- u 1) v w x)))]
               [b (lambda (q r x)
                    (let ([p (* q r)])
                      (e (* q r) p x)))]
               [c (lambda (x) (* 5 x))]
               [e (lambda (n p x)
                    (if (= n '0) 
                        (c p)
                        (o (- n 1) p x)))]
               [o (lambda (n p x) 
                    (if (= 0 n)
                        (c x)
                        (e (- n 1) p x)))])
        (let ([x 5])
          (a 3 2 1 x)))
      ((letrec ([length (lambda (ptr)
                          (if (null? ptr) 0 (+ 1 (length (cdr ptr)))))])
         length)
       '(5 10 11 5 15))
      (letrec ([count-leaves (lambda (p)
                               (if (pair? p)
                                   (+ (count-leaves (car p))
                                      (count-leaves (cdr p)))
                                   1))])
        (count-leaves 
          (cons 
            (cons '0 (cons '0 '0))
            (cons 
              (cons (cons (cons '0 (cons '0 '0)) '0) '0)
              (cons 
                (cons (cons '0 '0) (cons '0 (cons '0 '0)))
                (cons (cons '0 '0) '0))))))
      (letrec ([add1 (lambda (n) (+ n 1))]
               [map (lambda (f ls)
                      (if (null? ls) '() (cons (f (car ls)) (map f (cdr ls)))))]
               [sum (lambda (ls)
                        (if (null? ls) 0 (+ (car ls) (sum (cdr ls)))))])
        (let ([ls '(5 4 3 2 1)])
          (let ([ls (cons '10 (cons '9 (cons '8 (cons '7 (cons '6 ls)))))])
            (sum (map add1 ls)))))
      (letrec ([list-ref (lambda (ls offset)
                             (if (= offset 0)
                                 (car ls)
                                 (list-ref (cdr ls) (- offset 1))))]
               [add (lambda (v w) (+ v w))]
               [sub (lambda (v w) (- v w))]
               [mult (lambda (v w) (* v w))]
               [expt (lambda (v w) (if (= w 0) 1 (* v (expt v (- w 1)))))]
               [selector (lambda (op* sel rand1 rand2)
                             (if (null? sel)
                                 0
                                 (cons ((list-ref op* (car sel))
                                        (car rand1) (car rand2))
                                       (selector op* (cdr sel) (cdr rand1)
                                                 (cdr rand2)))))]
               [sum (lambda (ls) (if (pair? ls) (+ (car ls) (sum (cdr ls))) 0))])
        (sum (selector (cons add (cons sub (cons mult (cons expt '()))))
                       '(2 0 1 3 2) '(5 9 10 2 3) '(3 1 3 3 8))))
      (letrec ([thunk-num (lambda (n) (lambda () n))]
               [force (lambda (th) (th))]
               [add-ths (lambda (th1 th2 th3 th4)
                          (+ (+ (force th1) (force th2))
                             (+ (force th3) (force th4))))])
        (add-ths (thunk-num 5) (thunk-num 17) (thunk-num 7) (thunk-num 9)))
      (letrec ([x 7] [f (lambda () x)]) (f))
      ((lambda (y) ((lambda (f) (f (f y))) (lambda (y) y))) 4)
      (let ([double (lambda (a) (+ a a))]) (double 10))
      (let ([t #t] [f #f])
        (letrec ((even (lambda (x) (if (= x 0) t (odd (- x 1)))))
                 (odd (lambda (x) (if (= x 0) f (even (- x 1))))))
          (odd 13)))
      (letrec ([remq (lambda (x ls)
                       (if (null? ls)
                           '()
                           (if (eq? (car ls) x)
                               (remq x (cdr ls))
                               (cons (car ls) (remq x (cdr ls))))))])
        (remq 3 '(3 1 3)))
      (letrec ([make-param (lambda (val)
                             (let ([x val])
                               (letrec ([param (lambda (set val)
                                                 (if set (set! x val) x))])
                                 param)))])
        (let ([p (make-param 10)])
          (p #t 15)
          (p #f #f)))
      (let ([x 0])
        (letrec ([inc (lambda () (set! x (+ x 1)))]
                 [dec (lambda () (set! x (- x 1)))])
          (inc) (dec) (dec) (inc) (inc) (inc) (dec) (inc) x))
      (letrec ([gcd (lambda (x y)
                      (if (= y 0) 
                          x 
                          (gcd (if (> x y) (- x y) x)
                               (if (> x y) y (- y x)))))])
        (gcd 1071 1029))
      (letrec ([sub1 (lambda (n) (- n 1))]
               [fib (lambda (n)
                      (if (= 0 n)
                          0
                          (if (= 1 n)
                              1
                              (+ (fib (sub1 n))
                                 (fib (sub1 (sub1 n)))))))])
        (fib 10))
      (letrec ([ack (lambda (m n)
                      (if (= m 0)
                          (+ n 1)
                          (if (if (> m 0) (= n 0) #f)
                              (ack (- m 1) 1)
                              (ack (- m 1) (ack m (- n 1))))))])
        (ack 2 4))
      (letrec ([fib (lambda (n) 
                      (letrec ([fib (lambda (n a b)
                                      (if (= n 0)
                                          a
                                          (fib (- n 1) b (+ b a))))])
                        (fib n 0 1)))])
        (fib 5))
      ((((((lambda (x)
              (lambda (y)
                (lambda (z)
                  (lambda (w)
                    (lambda (u)
                      (+ x (+ y (+ z (+ w u)))))))))
           5) 6) 7) 8) 9)
      (let ([t #t] [f #f])
        (let ([bools (cons t f)] [id (lambda (x) (if (not x) f t))])
          (letrec
            ([even (lambda (x) (if (= x 0) (id (car bools)) (odd (- x 1))))]
             [odd (lambda (y) (if (= y 0) (id (cdr bools)) (even (- y 1))))])
            (odd 5))))
      (let ([x 7] [y 4])
        (or (and (fixnum? x) (= x 4) (fixnum? y) (= y 7))
            (and (fixnum? x) (= x 7) (fixnum? y) (= y 4))))
      (let ((y '()) (z 10))
        (let ((test-ls (cons 5 y)))
          (set! y (lambda (f)
                    ((lambda (g) (f (lambda (x) ((g g) x))))
                     (lambda (g) (f (lambda (x) ((g g) x)))))))
          (set! test-ls (cons z test-ls))
          (letrec ((length (lambda (ls)
                             (if (null? ls) 0 (+ 1 (length (cdr ls)))))))
            (let ((len (length test-ls)))
              (eq? (begin
                     (set! length (y (lambda (len)
                                       (lambda (ls)
                                         (if (null? ls)
                                             0
                                             (+ 1 (len (cdr ls))))))))
                     (length test-ls))
                   len)))))
      (letrec ([if-test (lambda (n x y)
                          (if (= n 0)
                              (vector-set! x 0 (+ (vector-ref x 0)
                                                  (vector-ref y 0)))
                              (vector-set! y 0 (+ (vector-ref y 0)
                                                  (vector-ref x 0))))
                          (vector-set! x 0 (+ (vector-ref x 0) n))
                          (if (if (= n (vector-ref y 0)) #f #t)
                              (+ n (vector-ref x 0))
                              (+ n (vector-ref y 0))))])
        (let ([q (make-vector 1)] [p (make-vector 1)])
          (vector-set! q 0 1)
          (vector-set! p 0 2)
          (if-test 3 q p)))
      (letrec ([if-test (lambda (n)
                          (let ([m (make-vector 1)]
                                [x (make-vector 1)]
                                [y (make-vector 1)])
                            (vector-set! m 0 n)
                            (vector-set! x 0 1)
                            (begin
                              (vector-set! y 0 1)
                              (if (eq? (vector-ref m 0) 0)
                                  (vector-set! (vector-ref x 0) 0
                                               (+ (vector-ref x 0)
                                                  (vector-ref y 0)))
                                  (vector-set! y 0 (+ (vector-ref y 0)
                                                      (vector-ref x 0))))
                              (vector-set! x 0 (+ (vector-ref x 0)
                                                  (vector-ref m 0))))
                            (if (if (eq? (vector-ref m 0) (vector-ref y 0)) #f #t)
                                (vector-set! m 0 (+ (vector-ref m 0)
                                                    (vector-ref x 0)))
                                (vector-set! m 0 (+ (vector-ref m 0)
                                                    (vector-ref y 0))))
                            (+ (vector-ref x 0) (vector-ref m 0))))])
        (if-test 1))
      (letrec ([f (lambda (x) (+ 1 x))]
               [g (lambda (x) (- x 1))]
               [t (lambda (x) (- x 1))]
               [j (lambda (x) (- x 1))]
               [i (lambda (x) (- x 1))]
               [h (lambda (x) (- x 1))])
        (let ([x 80])
          (let ([a (f x)]
                [b (g x)]
                [c (h (i (j (t x))))])
            (* a (* b (+ c 0))))))
      (let ([f (lambda (x) (+ 1 x))] [g (lambda (x) (- x 1))])
        (let ([x 80])
          (let ([a (f x)]
                [b (g x)]
                [c (letrec ([h (lambda (x) (- x 1))])
                     (h (letrec ([i (lambda (x) (- x 1))])
                          (i
                            (letrec ([t (lambda (x) (- x 1))]
                                     [j (lambda (x) (- x 1))])
                              (j (t x)))))))])
            (* a (* b (+ c 0))))))
      (letrec ([fact (lambda (n)
                       (if (= n 0)
                           1
                           (let ([t (- n 1)])
                             (let ([t (fact t)])
                               (* n t)))))])
        (fact 10))
      (letrec ([fib (lambda (n k)
                      (if (or (= n 0) (= n 1))
                          (k 1)
                          (fib (- n 1) (lambda (w)
                                         (fib (- n 2) (lambda (v)
                                                        (k (+ w v))))))))])
        (fib 10 (lambda (x) x)))
      (letrec ()
        (let ([n (let ([p (make-vector 1)]) (vector-set! p 0 1) p)])
          (let ([a 2])
            (let ([b 3])
              (vector-set! n 0 (+ (vector-ref n 0) 
                                  (if (= (+ (vector-ref n 0) b) b) 5 10)))
              (vector-set! n 0 (+ (vector-ref n 0) b)))
            (vector-set! n 0 (+ (vector-ref n 0) a)))
          (+ (vector-ref n 0) (vector-ref n 0))))
      (let ([dot-product (lambda (v1 v2)
                           (if (and (vector? v1) (vector? v2)
                                    (= (vector-length v1) (vector-length v2)))
                               (letrec ([f (lambda (i)
                                             (if (= i 0)
                                                 1
                                                 (let ([i (- i 1)])
                                                   (+ (* (vector-ref v1 i)
                                                         (vector-ref v2 i))
                                                      (f i)))))])
                                 (f (vector-length v1)))
                               #f))])
        (cons (dot-product '(1 2) '#(3 4))
              (cons (dot-product '#(1 2) '#(3 4 5))
                    (cons (dot-product '#(4 5 6 7) '#(2 9 8 1)) '()))))
      (letrec ([num-list? (lambda (ls)
                            (if (null? ls)
                                #t
                                (if (fixnum? (car ls))
                                    (num-list? (cdr ls))
                                    #f)))]
               [length (lambda (ls)
                         (if (null? ls)
                             0
                             (+ (length (cdr ls)) 1)))]
               [dot-prod (lambda (ls1 ls2)
                           (if (if (null? ls1) (null? ls2) #f)
                               0
                               (+ (* (car ls1) (car ls2))
                                  (dot-prod (cdr ls1) (cdr ls2)))))])
        (let ([ls1 '(1 2 3 4 5)]
              [ls2 '(5 4 3 2 1)])
          (if (if (if (eq? (num-list? ls1) #f) #f #t)
                  (if (if (eq? (num-list? ls2) #f) #f #t)
                      (= (length ls1) (length ls2))
                      #f)
                  #f)
              (dot-prod ls1 ls2)
              #f)))
      (letrec ([num-list? (lambda (ls)
                            (or (null? ls) 
                                (and (fixnum? (car ls)) (num-list? (cdr ls)))))]
               [map (lambda (f ls)
                        (if (null? ls) 
                            '()
                            (cons (f (car ls)) (map f (cdr ls)))))]
               [square (lambda (n) (* n n))])
        (let ([ls '(1 2 3 4 5)])
          (if (num-list? ls) (set-car! ls (map square ls)))
          ls))
      (letrec ([num-list? (lambda (ls)
                            (if (null? ls)
                                #t
                                (if (fixnum? (car ls))
                                    (num-list? (cdr ls))
                                    #f)))]
               [list-product (lambda (ls)
                               (if (null? ls)
                                   1
                                   (* (car ls) (list-product (cdr ls)))))])
        (let ([ls '(1 2 3 4 5)])
          (if (num-list? ls) (list-product ls) #f)))
      (letrec ([f (lambda (x y)
                      (if x (h (+ x y)) (g (+ x 1) (+ y 1))))]
               [g (lambda (u v)
                    (let ([a (+ u v)] [b (* u v)])
                      (letrec ([e (lambda (d)
                                    (let ([p (cons a b)])
                                      (letrec ([q (lambda (m)
                                                    (if (< m u)
                                                        (f m d)
                                                        (h (car p))))])
                                        (q (f a b)))))])
                        (e u))))]
               [h (lambda (w) w)])
        (f 4 5))
      (let ((y '())
            (z 10))
        (let ((test-ls (cons 5 y)))
          (set! y (lambda (f)
                    ((lambda (g) (f (lambda (x) ((g g) x))))
                     (lambda (g) (f (lambda (x) ((g g) x)))))))
          (set! test-ls (cons z test-ls))
          (letrec ((length (lambda (ls)
                              (if (null? ls) 0 (+ 1 (length (cdr ls)))))))
            (let ((len (length test-ls)))
              (eq? (begin
                    (set! length (y (lambda (len)
                                      (lambda (ls)
                                        (if (null? ls)
                                            0
                                            (+ 1 (len (cdr ls))))))))
                    (length test-ls))
                   len)))))
      (letrec ([curry-list
                 (lambda (x)
                   (lambda (y)
                     (lambda (z)
                       (lambda (w)
                         (cons x (cons y (cons z (cons w '()))))))))]
               [append (lambda (ls1 ls2)
                         (if (null? ls1)
                             ls2
                             (cons (car ls1)
                                   (append (cdr ls1) ls2))))])
        (append
          ((((curry-list 1) 2) 3) 4)
          ((((curry-list 5) 6) 7) 8)))
      (letrec ([quotient (lambda (x y)
                           (if (< x 0)
                               (- 0 (quotient (- 0 x) y))
                               (if (< y 0)
                                   (- 0 (quotient x (- 0 y)))
                                   (letrec ([f (lambda (x a)
                                                 (if (< x y)
                                                     a
                                                     (f (- x y) (+ a '1))))])
                                     (f x 0)))))])
        (let ([sub-interval 1])
          (letrec ([sub-and-continue (lambda (n acc k)
                                       (k (- n sub-interval) (* n acc)))]
                   [strange-fact (lambda (n acc)
                                   (if (= n 0)
                                     (lambda (proc) (proc acc))
                                     (sub-and-continue n acc strange-fact)))])
            (let ([x 20] [fact (let ([seed 1])
                                 (lambda (n) (strange-fact n seed)))])
              (let ([x (cons x (if #f #f))])
                (letrec ([answer-user (lambda (ans) (quotient ans (car x)))])
                  (let ([give-fact5-answer (fact 5)] [give-fact6-answer (fact 6)])
                    (begin
                      (set-car! x (give-fact5-answer answer-user))
                      (set-car! x (give-fact6-answer answer-user))
                      (car x)))))))))
      
      (letrec ([fib (lambda (x)
                      (let ([decrx (lambda () (lambda (i) (set! x (- x i))))])
                        (if (< x 2)
                            1
                            (+ (begin ((decrx) 1) (fib x))
                               (begin ((decrx) 1) (fib x))))))])
        (fib 10))
      ; test use of keywords/primitives as variables
      (let ([quote (lambda (x) x)]
            [let (lambda (x y) (- y x))]
            [if (lambda (x y z) (cons x z))]
            [cons (lambda (x y) (cons y x))]
            [+ 16])
        (set! + (* 16 2))
        (cons (let ((quote (lambda () 0))) +)
              (if (quote (not #f)) 720000 -1)))
      (letrec ([sum-all (lambda (x)
                          (if (fixnum? x)
                              x
                              (if (vector? x)
                                  (sum-vector x)
                                  (if (pair? x)
                                      (sum-pair x)
                                      (if (procedure? x)
                                          (sum-all (x))
                                          0)))))]
               [sum-vector (lambda (v)
                             (letrec ([l (lambda (v i)
                                           (if (= i 0) 
                                               0 
                                               (sum-all 
                                                 (vector-ref v (- i 1)))))])
                               (l v (vector-length v))))]
               [sum-pair (lambda (p)
                           (+ (sum-all (car p)) (sum-all (cdr p))))])
        (sum-all (lambda () '#((7 8 1) 
                               #(81 23 8)
                               #(#(#(12) 56) 18 ((1 2) (3 ((4)) 5)))))))
      (letrec ([div (lambda (d n)
                      (letrec ([f (lambda (d n q)
                                    (if (> n d)
                                        q
                                        (f (- d n) n (+ q 1))))])
                        (f d n 0)))])
        (letrec ([alloc (lambda (n) (make-vector (div n 8)))]
                 [mref (lambda (x y)
                         (if (vector? x)
                             (vector-ref x (div y 8))
                             (vector-ref y (div x 8))))]
                 [mset! (lambda (x y z)
                          (if (vector? x)
                              (vector-set! x (div y 8) z)
                              (vector-set! y (div x 8) z))
                          (if #f #f))])
          (letrec ([stack-push (lambda (self val)
                                 (mset! (mref self 16) (* (mref self 8) 8) val)
                                 (mset! self 8 (+ (mref self 8) 1))
                                 self)]
                   [stack-pop (lambda (self)
                                (mset! self 8 (- (mref 8 self) 1))
                                (mref (mref self 16) (* (mref self 8) 8)))]
                   [stack-top (lambda (self)
                                (mref (mref self 16) 
                                      (* (- (mref 8 self) 1) 8)))])
            (letrec ([stack-new
                       (let ([meths (alloc (* 3 8))])
                         (mset! meths 0 stack-push)
                         (mset! meths 8 stack-pop)
                         (mset! meths 16 stack-top)
                         (lambda (size)
                           (let ([self (alloc (* 3 8))])
                             (mset! self 0 meths)
                             (mset! self 8 0)
                             (mset! self 16 (alloc (* 8 size)))
                             self)))]
                     [invoke (lambda (obj meth-idx)
                               (mref (mref obj 0) (* meth-idx 8)))])
              (let ([s1 (stack-new 10)])
                (begin
                  ((invoke s1 0) s1 10) ;; push '10
                  ((invoke s1 0) s1 20) ;; push '20
                  ((invoke s1 0) s1 30) ;; push ... well you get the idea
                  ((invoke s1 0) s1 40)
                  ((invoke s1 0) s1 0)
                  ((invoke s1 0) s1 60)
                  ((invoke s1 0) s1 70)
                  ((invoke s1 0) s1 80)
                  ((invoke s1 0) s1 90)
                  ((invoke s1 0) s1 100)
                  (let ([s2 (stack-new 6)])
                    (begin
                      ((invoke s2 0) s2 ((invoke s1 1) s1)) ;; push pop
                      ((invoke s1 1) s1) ;; pop
                      ((invoke s2 0) s2 ((invoke s1 1) s1))
                      ((invoke s1 1) s1) ;; pop
                      ((invoke s2 0) s2 ((invoke s1 1) s1))
                      ((invoke s1 1) s1) ;; pop
                      ((invoke s2 0) s2 ((invoke s1 1) s1))
                      ((invoke s1 1) s1) ;; pop
                      ((invoke s2 0) s2 ((invoke s1 1) s1))
                      ((invoke s2 0) s2 ((invoke s1 1) s1))
                      (let ([x (+ ((invoke s2 1) s2) ((invoke s2 1) s2))])
                        (* (+ (let ([x (+ ((invoke s2 2) s2)
                                          ((invoke s2 2) s2))])
                                (- x (+ ((invoke s2 1) s2) ((invoke s2 1) s2))))
                              (let ([x (+ ((invoke s2 2) s2)
                                          ((invoke s2 2) s2))])
                                (- (+ ((invoke s2 1) s2) ((invoke s2 1) s2)) x)))
                           x))))))))))
      (if (lambda () 1)
          (let ((a 2))
            (if (if ((lambda (x)
                       (let ((x (set! a (set! a 1))))
                         x)) 1)
                    (if (eq? a (void))
                        #t
                        #f)
                    #f)
                #36rgood        ; dyb: cannot use symbols, so use radix 36
                #36rbad)))
  
     ; contributed by Ryan Newton
      (letrec
        ([dropsearch
           (lambda (cell tree)
             (letrec
               ([create-link
                    (lambda (node f)
                      (lambda (g)
                        (if (not (pair? node))
                            (f g)
                            (if (eq? node cell)
                                #f
                                (f (create-link (car node)
                                                (create-link (cdr node) g)))))))]
                [loop
                  (lambda (link)
                    (lambda ()
                      (if link
                          (loop (link (lambda (v) v)))
                          #f)))])
               (loop (create-link tree (lambda (x) x)))))]
           [racethunks
             (lambda (thunkx thunky)
               (if (if thunkx thunky #f)
                   (racethunks (thunkx) (thunky))
                   (if thunky
                       #t
                       (if thunkx
                           #f
                           '()))))]
           [higher?
             (lambda (x y tree)
               (racethunks (dropsearch x tree)
                           (dropsearch y tree)))]
           [under?
             (lambda (x y tree)
               (racethunks (dropsearch x y)
                           (dropsearch x tree)))]
           [explore
             (lambda (x y tree)
               (if (not (pair? y))
                   #t
                   (if (eq? x y)
                       #f    ;This will take out anything that points to itself
                       (let ((result (higher? x y tree)))
                         (if (eq? result #t)
                             (if (explore y (car y) tree)
                                 (explore y (cdr y) tree)
                                 #f)
                             (if (eq? result #f)
                                 (process-vertical-jump x y tree)
                                 (if (eq? result '())
                                     (process-horizontal-jump x y tree)
                                     )))))))]
           [process-vertical-jump
             (lambda (jumpedfrom jumpedto tree)
               (if (under? jumpedfrom jumpedto tree)
                   #f
                   (fullfinite? jumpedto)))]
           [process-horizontal-jump
             (lambda (jumpedfrom jumpedto tree)
               (fullfinite? jumpedto))]
           [fullfinite?
             (lambda (pair)
               (if (not (pair? pair))
                   #t
                   (if (explore pair (car pair) pair)
                       (explore pair (cdr pair) pair)
                       #f)))])
         (cons
           (fullfinite? (cons 1 2))
           (cons
             (fullfinite? (let ((x (cons 1 2))) (set-car! x x) x))
             (cons
               (fullfinite? (let ([a (cons 0 0)] [b (cons 0 0)] [c (cons 0 0)])
                              (set-car! a b) (set-cdr! a c) (set-cdr! b c)
                              (set-car! b c) (set-car! c b) (set-cdr! c b) a))
               '()))))
      (letrec ([zero? (lambda (x) (= x 0))]
           [sub1 (lambda (n) (- n 1))]
           [assq (lambda (sym al)
                   (if (null? al)
                       #f
                       (let ([entry (car al)])
                         (if (eq? sym (car entry))
                             (cdr entry)
                             (assq sym (cdr al))))))]
           [map (lambda (p ls)
                  (if (null? ls)
                      '()
                      (cons (p (car ls)) (map p (cdr ls)))))]
           [snoc (lambda (ls sym)
                   (if (null? ls)
                       (cons sym '())
                       (cons (car ls) (snoc (cdr ls) sym))))]
           [iota (lambda (n)
                   (if (zero? n)
                       '(0)
                       (snoc (iota (sub1 n)) n)))]
           [fib (lambda (n)
                  (if (zero? n)
                      0
                      (if (= n 1)
                          1
                          (+ (fib (- n 1)) (fib (- n 2))))))]
           [bounded-memoize (lambda (p bound)
                              (let ([memo '()])
                                (lambda (arg)
                                  (if (if (< arg bound) (assq arg memo) #f)
                                      (assq arg memo)
                                      (let ([ans (p arg)])
                                        (if (< arg bound)
                                            (set! memo (cons (cons arg ans) memo)))
                                        ans)))))])
        (set! fib (bounded-memoize fib 5))
        (map fib (iota 10)))
  
      ;; Francis Fernandez
      (and (+ ((if (not (cons '1 '(2))) 
                   '#t 
                   (letrec ([f.1 '3] [f.2 (lambda (x.3) (+ x.3 '4))])
                     f.2))
               '5) '6) '#f)
  
      ;; Thiago Rebello
      (let ([a 5]
            [b 4])
        (letrec ([c (lambda(d e) (* d e))]
                 [f (lambda(g h) (cons g h))])
          (if (or (> (c a b) 15) (= (c a b) 20))
              (f a b))))
  
      ;; Yin Wang
      (let ([begin (lambda (x y) (+ x y))]
            [set! (lambda (x y) (* x y))])
        (let ([lambda (lambda (x) (begin 1 x))])
          (let ([lambda (lambda (set! 1 2))])
            (let ([let (set! lambda lambda)])
              (begin let (set! lambda (set! 4 (begin 2 3))))))))
  
      ;; Ben Peters
      (let ([x '(4 5 6)]
            [y '(7 8 9)])
        (cons 1 (cons 2 (cons 3 (cons (car x) (cons (car (cdr x)) (cons (car (cdr (cdr x))) y)))))))
      
      ;; Patrick Jensen
      (let ([a 1])
        (letrec ([add1 (lambda (b) (+ b 1))]
                 [sub1 (lambda (b) (- b 1))])
          (let ([c (lambda (a)
                     (if (or (not (= a 1)) (and (> a 1) (< a 4)))
                         (add1 a)
                         (sub1 a)))])
            (let ([d (c a)] [e (c (add1 a))] [f (c (sub1 a))])
              (cons d (cons e (cons f '())))))))
  
      ;; Melanie Dybvig
      (letrec ((not (lambda (x) x))
               (a (if (< (* 3 3) (+ 3 3)) #t #f))
               (b 7))
        (if (not a)
            (set! b (+ b 2))
            (if (not (not a))
                (set! b (- b 2))))
        (cons b (or (not (not a)) (not a))))
  
      ;; Lindsey Kuper
      (let ([foo (lambda (lambda)
                   (lambda))])
        (let ([lambda foo]
              [bar (lambda () #t)])
          (foo bar)))
   
      ;; Yu-Shan Huang
      (let ([x 1])
        (let ([x 2])
          (if (and (< x 5) (not #f))
            (set! x 6)))
        x)
  
      ;; Chabane Maidi
      (letrec ([merge (lambda (ls ls2)
                        (if (null? ls)
                            ls2
                            (if (null? ls2)
                                ls
                                (if (< (car ls) (car ls2))
                                    (cons (car ls) (merge (cdr ls) ls2))
                                    (cons (car ls2) (merge ls (cdr ls2)))))))]
               [sort (lambda (ls)
                       (if (null? ls)
                           ls
                           (if (null? (cdr ls))
                               ls
                               (let ([halves (halves ls '() '() #t)])
                                 (let ([first (car halves)]
                                       [second (car (cdr halves))])
                                   (merge (sort first) (sort second)))))))]
               [halves (lambda (ls first second first?)
                         (if (null? ls)
                             (cons first (cons second '()))
                             (if first?
                                 (halves (cdr ls) (cons (car ls) first) second #f)
                                 (halves (cdr ls) first (cons (car ls) second) #t))))]
               [pend (lambda (ls ls2)
                       (if (null? ls)
                           ls2
                           (cons (car ls) (pend (cdr ls) ls2))))])
        (pend (sort '(1 5 5 8 2 3 9)) (sort '(5 9 5 7 7 8 7))))
  
      ;; Kewal Karavinkoppa
      (letrec ([depth (lambda (ls)
                        (if (null? ls)
                            1
                            (if (pair? (car ls))
                                (let ([l ((lambda (m)
                                            (+ m 1))
                                          (depth (car ls)))]
                                      [r (depth (cdr ls))])
                                  (if (< l r) r l))
                                (depth (cdr ls)))))])
        (depth '(1 2 (3 (4 (5 (6 7)))))))
  
      ;; Brennon York
      ((lambda (x) (if (if (eq? x 5) x (and x 1 2 3 4 (or 6 7 8 9))) 3)) 4)
  
      ;; Nilesh Mahajan
      (letrec ([F (lambda (func-arg)
                    (lambda (n)
                      (if (= n 0)
                          1
                          (* n (func-arg (- n 1))))))])
        (letrec ([Y (lambda (X)
                      ((lambda (procedure)
                         (X (lambda (arg) ((procedure procedure) arg))))
                       (lambda (procedure)
                         (X (lambda (arg) ((procedure procedure) arg))))))])
          (letrec ([fact (Y F)])
            (fact 5))))
  
      ;; Joseph Knecht
      (letrec ([f (lambda () '(1 . 2))]) (eq? (f) (f)))
  
      ;; Emily Lyons
      (letrec ([extend (lambda (num alist)
                         (if (null? alist)
                             (cons (cons num 1) '())
                             (if (= num (car (car alist)))
                                 (cons (cons num (+ 1 (cdr (car alist))))
                                       (cdr alist))
                                 (cons (car alist)
                                       (extend num (cdr alist))))))]
               [loop (lambda (ls alist)
                       (if (null? ls)
                           alist
                           (loop (cdr ls) (extend (car ls) alist))))])
        (loop '(1 3 4 5 5 4 5 2 3 4 1) '()))
      ))

  (define last-test
    (make-parameter 0
      (lambda (x)
        (unless (and (integer? x) (exact? x)) (errorf 'last-test "expected exact integer, but got ~s" x))
        x)))

  (define test-all
    (case-lambda
      [() (test-all #f)]
      [(noisy?)
       (for-all
         (lambda (t)
           (when noisy? (pretty-print t))
           (let ([expected (eval t)]
                 [actual (guard (e [else (printf "test-exception evaluating:~%") (pretty-print t) (raise e)])
                           (tiny-compile t))])
             (unless (or (equal? expected actual) (equal? actual '#(exception)))
               (printf "test-failed: expected ~s, but got ~s but got:~%" expected actual)
               (pretty-print t)
               (errorf 'test-all "testing failed"))))
         tests)]))

  (define (analyze-all)
    (let ([c 1])
      (for-all
        (lambda (t)
          (let ([expected (eval t)]
                [actual (guard (e [else (printf "E") (flush-output-port) '#(exception)]) (tiny-compile t))])
            (cond
              [(equal? expected actual) (printf ".") (flush-output-port)]
              [(equal? actual '#(exception)) (void)]
              [else (printf "F") (flush-output-port)])
            (when (= c 50) (newline) (set! c 0))
            (set! c (+ c 1))))
        tests)))
  )

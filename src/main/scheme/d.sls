;; Primitives needed for psyntax:
;;
;; listed? | primitive
;; --------+-----------------
;; n       | &condition-rcd
;; n       | &condition-rtd
;; p       | +
;; p       | -
;; p       | <=
;; p       | =
;; p       | >
;; p       | >=
;; l       | append
;; p       | apply
;; ?       | assertion-violation
;; l       | assq
;; p       | boolean?
;; p       | bytevector?
;; l       | caar
;; l       | caddr
;; l       | cadr
;; l       | call-with-values
;; p       | car
;; l       | cdar
;; l       | cddr
;; p       | cdr
;; p       | char->integer
;; p       | char<=?
;; p       | char?
;; ?       | command-line
;; ?       | condition
;; ?       | condition-accessor
;; ?       | condition-predicate
;; p       | cons
;; l       | cons*
;; ?       | display
;; l       | dynamic-wind
;; p       | eof-object?
;; p       | eq?
;; l       | equal?
;; l       | eqv?
;; ?       | error
;; ?       | eval-core
;; p       | exact?
;; l       | exists
;; ?       | exit
;; ?       | file-exists?
;; l       | for-all
;; l       | for-each
;; ?       | gensym
;; l       | hashtable-entries
;; l       | hashtable-ref
;; l       | hashtable-set!
;; p       | integer->char
;; p       | integer?
;; l       | length
;; l       | list
;; l       | list->vector
;; l       | list?
;; n       | make-assertion-violation
;; p       | make-eq-hashtable
;; n       | make-irritants-condition
;; n       | make-message-condition
;; n       | make-record-constructor-descriptor
;; n       | make-record-type-descriptor
;; n       | make-syntax-violation
;; n       | make-undefined-violation
;; p       | make-vector
;; n       | make-who-condition
;; l       | map
;; l       | member
;; l       | memq
;; l       | memv
;; n       | newline
;; p       | null?
;; l       | number?
;; n       | open-string-output-port
;; p       | pair?
;; n       | pretty-print
;; p       | procedure?
;; p       | quotient
;; n       | raise
;; n       | read
;; n       | record-accessor
;; n       | record-constructor
;; n       | record-predicate
;; p       | remainder
;; l       | remq
;; l       | reverse
;; p       | set-car!
;; p       | set-cdr!
;; p       | set-symbol-value!
;; l       | string
;; l       | string->list
;; p       | string->symbol
;; l       | string-append
;; p       | string?
;; p       | symbol->string
;; p       | symbol-value
;; p       | symbol?
;; l       | values
;; l       | vector
;; l       | vector->list
;; l       | vector-for-each
;; p       | vector-length
;; l       | vector-map
;; p       | vector-ref
;; p       | vector-set!
;; p       | vector?
;; p       | void
;; n       | with-input-from-file
;; n       | write
;; l       | zero?

(library (d)
  (export immediate? datatype? primitive? pure-primitive? value-primitive?
    predicate-primitive? effect-primitive? primitive->primitive-info
    primitive-info? primitive-info-name primitive-info-arity* arity-matches?
    primitive-info-kind make-primitive-info exact-integer?)
  (import (rnrs) (only (chezscheme) module eq-hashtable? errorf))

  (define target-datatype-source-preds
    (let ([ls '()])
      (case-lambda
        [() ls]
        [(pred) (set! ls (cons pred ls))])))

  (define-record-type datatype-info
    (nongenerative)
    (fields name cons pred? ops))

  (define-record-type primitive-info
    (nongenerative)
    (fields name arity* kind))

  (define datatype-prim->prim-info
    (lambda (dt name)
      (find (lambda (pr) (eq? (primitive-info-name pr) name)) (datatype-info-ops dt))))

  (define target-primitives (make-hashtable symbol-hash eq?))

  (define-syntax define-datatype
    (lambda (x)
      (syntax-case x ()
        [(_ name [cons c-arity c-arities ...] [pred? target-pred?] [op op-arity op-arities ... kind] ...)
         (with-syntax ([(t-cons t-pred? t-op* ...) (generate-temporaries #'(cons pred? op ...))])
           #'(begin
               (define ignore (target-datatype-source-preds pred?))
               (define datatype
                 (make-datatype-info 'name 'cons 'pred?
                   (list
                     (make-primitive-info 'cons (list c-arity c-arities ...) 'value)
                     (make-primitive-info 'pred? (list 1) 'predicate)
                     (make-primitive-info 'op (list op-arity op-arities ...) 'kind) ...)))
               (define t-cons (hashtable-set! target-primitives 'cons (datatype-prim->prim-info datatype 'cons)))
               (define t-pred? (hashtable-set! target-primitives 'pred? (datatype-prim->prim-info datatype 'pred?)))
               (define t-op* (hashtable-set! target-primitives 'op (datatype-prim->prim-info datatype 'op)))
               ...))]
        [(_ name [cons c-arity c-arities ...] pred? [op op-arity op-arities ... kind] ...)
         #'(define-datatype name [cons c-arity c-arities ...] [pred? pred?] [op op-arity op-arities ... kind] ...)] )))

  (define-datatype pair [cons 2] [pair? target-pair?] [car 1 value] [cdr 1 value] [set-car! 2 effect] [set-cdr! 2 effect])
  (define-datatype vector [make-vector 1 2] [vector? target-vector?] [vector-length 1 value] [vector-ref 2 value] [vector-set! 3 effect])
  (define-datatype string [make-string 1 2] string? [string-length 1 value] [string-ref 2 value] [string-set! 3 effect])
  (define-datatype symbol [string->symbol 1] symbol? [symbol->string 1 value] [symbol-hash 1 value] [symbol-value 1 value] [set-symbol-value! 2 effect])
  (define-datatype char [integer->char 1] char? [char->integer 1 value] [char<=? -2 predicate])
  (define-datatype bytevector [make-bytevector 1 2] bytevector?)
  (define-datatype eq-hashtable [make-eq-hashtable 0 1] eq-hashtable? [eq-hashtable-ref 3 value] [eq-hashtable-set! 3 effect] [eq-hashtable-entries 1 value])

  (define-syntax define-primitive
    (lambda (x)
      (syntax-case x ()
        [(_ name arity arities ... kind)
         (with-syntax ([(t-name) (generate-temporaries #'(name))])
           #'(define t-name (hashtable-set! target-primitives 'name (make-primitive-info 'name (list arity arities ...) 'kind))))])))

  (define-primitive + -1 value)
  (define-primitive - -2 value)
  (define-primitive * -1 value)
  (define-primitive void 0 value)

  (define-primitive < -2 predicate)
  (define-primitive <= -2 predicate)
  (define-primitive = -2 predicate)
  (define-primitive >= -2 predicate)
  (define-primitive > -2 predicate)
  (define-primitive eq? 2 predicate)
  (define-primitive boolean? 1 predicate)
  (define-primitive fixnum? 1 predicate)
  (define-primitive null? 1 predicate)
  (define-primitive procedure? 1 predicate)

  (define-primitive apply -3 value)
  (define-primitive eof-object? 1 predicate)
  (define-primitive exact? 1 predicate)
  (define-primitive integer? 1 predicate)
  (define-primitive quotient 2 value)
  (define-primitive remainder 2 value)

  (define-primitive assertion-violation -3 effect)
  (define-primitive command-line 0 1 value)
  (define-primitive condition -1 value)
  (define-primitive condition-accessor 2 value)
  (define-primitive condition-predicate 1 value)
  (define-primitive display 1 2 effect)
  (define-primitive error -3 effect)
  (define-primitive eval-core 1 value)
  (define-primitive exit -1 effect)
  (define-primitive file-exists? 1 2 predicate)
  (define-primitive gensym 0 1 3 value)

  (define-primitive raise 1 effect)

  (define-primitive $make-procedure 2 value)
  (define-primitive $procedure-code 1 value)
  (define-primitive $procedure-ref 2 value)
  (define-primitive $procedure-set! 3 effect)

  (define primitive?
    (lambda (x)
      (and (primitive->primitive-info x) #t)))

  (define pure-primitive?
    (lambda (x)
      ;; bad proxy for pure, but using it for the moment
      (or (value-primitive? x) (predicate-primitive? x))))

  (define value-primitive?
    (lambda (x)
      (cond
        [(primitive-info? x) (eq? (primitive-info-kind x) 'value)]
        [(primitive->primitive-info x) => value-primitive?]
        [else #f])))

  (define predicate-primitive?
    (lambda (x)
      (cond
        [(primitive-info? x) (eq? (primitive-info-kind x) 'predicate)]
        [(primitive->primitive-info x) => predicate-primitive?]
        [else #f])))

  (define effect-primitive?
    (lambda (x)
      (cond
        [(primitive-info? x) (eq? (primitive-info-kind x) 'effect)]
        [(primitive->primitive-info x) => effect-primitive?]
        [else #f])))

  (define primitive->primitive-info
    (lambda (x)
      (hashtable-ref target-primitives x #f)))

  (define arity-matcher
    (lambda (len)
      (lambda (arity)
        (if (fx<? arity 0)
            (fx>=? len (fx- (fx- arity) 1))
            (fx=? len arity)))))

  (define $arity-matches?
    (lambda (ls len)
      (and (find (arity-matcher len) ls) #t)))

  (define arity-matches?
    (lambda (x y)
      (let ([len (if (fixnum? y) y (length y))])
        (cond
          [(eq? x #f) #f]
          [(symbol? x) (arity-matches? (primitive->primitive-info x) len)]
          [(primitive-info? x) ($arity-matches? (primitive-info-arity* x) len)]
          [(list? x) ($arity-matches? x len)]
          [(fixnum? x) ($arity-matches? (list x) len)]
          [else (errorf 'arity-matches? "unexpected source for arity check ~s" x)]))))

  (define exact-integer?
    (lambda (x)
      (and (integer? x) (exact? x))))

  (define target-fixnum?
    (lambda (x)
      (and (exact-integer? x)
           (<= (- (expt 2 60)) x (- (expt 2 61) 1)))))

  (define immediate?
    (lambda (x)
      (or (target-fixnum? x)
          (null? x)
          (boolean? x))))

  (define datatype?
    (lambda (x)
      (or (immediate? x)
          (exists (lambda (p) (p x)) (target-datatype-source-preds)))))
  
  (define target-pair?
    (lambda (x)
      (and (pair? x)
           (datatype? (car x))
           (datatype? (cdr x)))))

  (define target-vector?
    (lambda (x)
      (and (vector? x)
           (for-all datatype? (vector->list x)))))

  (define library-entries (make-hashtable symbol-hash eq?))

  (define-syntax define-library-entry
    (lambda (x)
      (syntax-case x ()
        [(_ name e)
         #'(define ignore (hashtable-set! library-entries 'name 'e))])))

  (define-library-entry append
    (case-lambda
      [() '()]
      [(x) x]
      [(x y) (letrec ([f (lambda (x) (if (null? x) y (cons (car x) (f (cdr x)))))]) (f x))]
      [(x . rest) (append x (apply append rest))]))

  (define-library-entry assq
    (lambda (x as*)
      (letrec ([f (lambda (as*)
                    (if (null? as*)
                        #f
                        (let ([as (car as*)])
                          (if (eq? (car as) x)
                              as
                              (f (cdr as*))))))])
        (f as*))))

  (define-library-entry caar (lambda (x) (car (car x))))
  (define-library-entry cadr (lambda (x) (car (cdr x))))
  (define-library-entry cdar (lambda (x) (cdr (car x))))
  (define-library-entry cddr (lambda (x) (cdr (cdr x))))

  (define-library-entry caaar (lambda (x) (car (car (car x)))))
  (define-library-entry caadr (lambda (x) (car (car (cdr x)))))
  (define-library-entry cadar (lambda (x) (car (cdr (car x)))))
  (define-library-entry caddr (lambda (x) (car (cdr (cdr x)))))
  (define-library-entry cdaar (lambda (x) (cdr (car (car x)))))
  (define-library-entry cdadr (lambda (x) (cdr (car (cdr x)))))
  (define-library-entry cddar (lambda (x) (cdr (cdr (car x)))))
  (define-library-entry cdddr (lambda (x) (cdr (cdr (cdr x)))))

  (define-library-entry caaaar (lambda (x) (car (car (car (car x))))))
  (define-library-entry caaadr (lambda (x) (car (car (car (cdr x))))))
  (define-library-entry caadar (lambda (x) (car (car (cdr (car x))))))
  (define-library-entry caaddr (lambda (x) (car (car (cdr (cdr x))))))

  (define-library-entry cadaar (lambda (x) (car (cdr (car (car x))))))
  (define-library-entry cadadr (lambda (x) (car (cdr (car (cdr x))))))
  (define-library-entry caddar (lambda (x) (car (cdr (cdr (car x))))))
  (define-library-entry cadddr (lambda (x) (car (cdr (cdr (cdr x))))))

  (define-library-entry cdaaar (lambda (x) (cdr (car (car (car x))))))
  (define-library-entry cdaadr (lambda (x) (cdr (car (car (cdr x))))))
  (define-library-entry cdadar (lambda (x) (cdr (car (cdr (car x))))))
  (define-library-entry cdaddr (lambda (x) (cdr (car (cdr (cdr x))))))

  (define-library-entry cddaar (lambda (x) (cdr (cdr (car (car x))))))
  (define-library-entry cddadr (lambda (x) (cdr (cdr (car (cdr x))))))
  (define-library-entry cdddar (lambda (x) (cdr (cdr (cdr (car x))))))
  (define-library-entry cddddr (lambda (x) (cdr (cdr (cdr (cdr x))))))

  (define-library-entry call-with-values
    (lambda (producer consumer)
      (apply consumer (producer))))

  (define-library-entry cons*
    (case-lambda
      [(d) d]
      [(a d) (cons a d)]
      [(a . rest) (cons a (apply cons* rest))]))

  (define-library-entry dynamic-wind ;; without call/cc can be pretty simple
    (lambda (entry f exit)
      (entry)
      (f)
      (exit)))

  (define-library-entry equal?
    (lambda (x y)
      (if (eq? x y)
          #t
          (if (pair? x)
              (if (pair? y)
                  (if (equal? (car x) (car y))
                      (equal? (cdr x) (cdr y))
                      #f)
                  #f)
              (if (vector? x)
                  (if (vector? y)
                      (let ([len (vector-length x)])
                        (if (= len (vector-length y))
                            (letrec ([f (lambda (n)
                                          (if (= n 0)
                                              #t
                                              (let ([n (- n 1)])
                                                (if (equal? (vector-ref x n) (vector-ref y n))
                                                    (f n)
                                                    #f))))])
                              (f len))
                            #f))
                      #f)
                  (if (string? x)
                      (if (string? y)
                          (let ([len (string-length x)])
                            (if (= len (string-length y))
                                (letrec ([f (lambda (n)
                                              (if (= n 0)
                                                  #t
                                                  (let ([n (- n 1)])
                                                    (if (equal? (string-ref x n) (string-ref y n))
                                                        (f n)
                                                        #f))))])
                                  (f len))
                                #f))
                          #f)
                      (if (bytevector? x)
                          (if (bytevector? y)
                              (let ([len (bytevector-length x)])
                                (if (= len (bytevector-length y))
                                    (letrec ([f (lambda (n)
                                                  (if (= n 0)
                                                      #t
                                                      (let ([n (- n 1)])
                                                        (if (equal? (bytevector-u8-ref x n) (bytevector-u8-ref y n))
                                                            (f n)
                                                            #f))))])
                                      (f len))
                                    #f))
                              #f)
                          #f)))))))

  (define-library-entry eqv?
    (lambda (x y)
      (eq? x y)))

  (define-library-entry exists
    (case-lambda
      [(p ls) (letrec ([f (lambda (ls)
                            (if (null? ls)
                                #f
                                (if (p (car ls))
                                    #t
                                    (f (cdr ls)))))])
                (f ls))]
      [(p ls0 ls1) (letrec ([f (lambda (ls0 ls1)
                                 (if (null? ls0)
                                     #f
                                     (if (p (car ls0) (car ls1))
                                         #t
                                         (f (cdr ls0) (cdr ls1)))))])
                     (f ls0 ls1))]
      [(p ls . rest) (letrec ([f (lambda (ls rest)
                                    (if (null? ls)
                                        #f
                                        (if (apply p (car ls) (map car rest))
                                            #t
                                            (f (cdr ls) (map cdr rest)))))])
                        (f ls rest))]))

  (define-library-entry for-all
    (case-lambda
      [(p ls) (letrec ([f (lambda (ls)
                            (if (null? ls)
                                #t
                                (if (p (car ls))
                                    (f (cdr ls))
                                    #f)))])
                (f ls))]
      [(p ls0 ls1) (letrec ([f (lambda (ls0 ls1)
                                 (if (null? ls0)
                                     #t
                                     (if (p (car ls0) (car ls1))
                                         (f (cdr ls0) (cdr ls1))
                                         #f)))])
                     (f ls0 ls1))]
      [(p ls . rest) (letrec ([f (lambda (ls rest)
                                   (if (null? ls)
                                       #t
                                       (if (apply p (car ls) (map car rest))
                                           (f (cdr ls) (map cdr rest))
                                           #f)))])
                       (f ls rest))]))

  (define-library-entry for-each
    (case-lambda
      [(p ls) (letrec ([f (lambda (ls)
                            (if (null? ls)
                                (void)
                                (begin
                                  (p (car ls))
                                  (f (cdr ls)))))])
                (f ls))]
      [(p ls0 ls1) (letrec ([f (lambda (ls0 ls1)
                                 (if (null? ls0)
                                     (void)
                                     (begin
                                       (p (car ls0) (car ls1))
                                       (f (cdr ls0) (cdr ls1)))))])
                     (f ls0 ls1))]
      [(p ls . rest) (letrec ([f (lambda (ls rest)
                                   (if (null? ls)
                                       (void)
                                       (begin
                                         (apply p (car ls) (map car rest))
                                         (f (cdr ls) (map cdr rest)))))])
                       (f ls rest))]))

  (define-library-entry hashtable-entries
    (lambda (ht)
      (eq-hashtable-entries ht)))

  (define-library-entry hashtable-ref
    (lambda (ht key default)
      (eq-hashtable-ref ht key default)))

  (define-library-entry hashtable-set!
    (lambda (ht key value)
      (eq-hashtable-set! ht key value)))

  (define-library-entry length
    (lambda (ls)
      (if (pair? ls)
          (+ 1 (length (cdr ls)))
          0)))

  (define-library-entry list (lambda ls ls))

  (define-library-entry list->vector
    (lambda (ls)
      (letrec ([f (lambda (ls n)
                    (if (null? ls)
                        (make-vector n)
                        (let ([v (f (cdr ls) (+ n 1))])
                          (vector-set! v n (car ls))
                          v)))])
        (f ls 0))))

  (define-library-entry list?
    (lambda (x)
      (if (pair? x)
          (list? (cdr x))
          (null? x))))

  (define-library-entry map
    (case-lambda
      [(p ls)
       (letrec ([f (lambda (ls)
                     (if (null? ls)
                         '()
                         (cons (p (car ls)) (f (cdr ls)))))])
         (f ls))]
      [(p ls0 ls1)
       (letrec ([f (lambda (ls0 ls1)
                     (if (null? ls0)
                         '()
                         (cons (p (car ls0) (car ls1)) (f (cdr ls0) (cdr ls1)))))])
         (f ls0 ls1))]
      [(p ls . rest)
       (letrec ([f (lambda (ls rest)
                     (if (null? ls)
                         '()
                         (cons (apply p (car ls) (map car rest)) (f (cdr ls) (map cdr rest)))))])
         (f ls rest))]))

  (define-library-entry member
    (lambda (x ls)
      (letrec ([f (lambda (ls)
                    (if (null? ls)
                        #f
                        (if (equal? x (car ls))
                            ls
                            (f (cdr ls)))))])
        (f ls))))

  (define-library-entry memq
    (lambda (x ls)
      (letrec ([f (lambda (ls)
                    (if (null? ls)
                        #f
                        (if (eq? x (car ls))
                            ls
                            (f (cdr ls)))))])
        (f ls))))

  (define-library-entry memv
    (lambda (x ls)
      (letrec ([f (lambda (ls)
                    (if (null? ls)
                        #f
                        (if (eqv? x (car ls))
                            ls
                            (f (cdr ls)))))])
        (f ls))))

  (define-library-entry number?
    (lambda (x)
      (fixnum? x)))

  (define-library-entry remq
    (lambda (x ls)
      (letrec ([f (lambda (ls)
                    (if (null? ls)
                        '()
                        (let ([y (car ls)])
                          (if (eq? x y)
                              (f (cdr ls))
                              (cons y (f (cdr ls)))))))])
        (f ls))))

  (define-library-entry reverse
    (lambda (ls)
      (letrec ([f (lambda (ls rls)
                    (if (null? ls)
                        rls
                        (f (cdr ls) (cons (car ls) rls))))])
        (f ls '()))))

  (define-library-entry list->string
    (lambda (ls)
      (letrec ([f (lambda (ls n)
                    (if (null? n)
                        (make-string n)
                        (let ([str (f (cdr ls) (+ n 1))])
                          (string-set! str n (car ls))
                          str)))])
        (f ls))))

  (define-library-entry string (lambda ls (list->string ls)))

  (define-library-entry string->list
    (lambda (str)
      (letrec ([f (lambda (n ls)
                    (if (= n 0)
                        ls
                        (let ([n (- n 1)])
                          (f n (cons (string-ref str n) ls)))))])
        (f (string-length str) '()))))

  (define-library-entry string-append
    (case-lambda
      [() '""]
      [(x) x]
      [(x y) (let ([len-x (string-length x)]
                   [len-y (string-length y)])
               (let ([str (make-string (+ len-x len-y))])
                 (letrec ([f (lambda (n)
                               (if (= n len-x)
                                   (letrec ([f (lambda (n i)
                                                 (if (= i len-y)
                                                     str
                                                     (begin
                                                       (string-set! str n (string-ref y i))
                                                       (f (+ n 1) (+ i 1)))))])
                                     (f n 0))
                                   (begin
                                     (string-set! str n (string-ref x n))
                                     (f (+ n 1)))))])
                   (f 0))))]
      [(x . rest) (string-append x (apply string-append rest))]))

  (define-library-entry values (lambda ls ls))

  (define-library-entry vector (lambda ls (list->vector ls)))

  (define-library-entry vector->list
    (lambda (v)
      (letrec ([f (lambda (n ls)
                    (if (= n 0)
                        ls
                        (let ([n (- n 1)])
                          (f n (cons (vector-ref v n) ls)))))])
        (f (vector-length v)))))

  (define-library-entry vector-for-each
    (case-lambda
      [(p v)
       (let ([len (vector-length v)])
         (letrec ([f (lambda (n)
                       (if (= n len)
                           (void)
                           (begin
                             (p (vector-ref v n))
                             (f (+ n 1)))))])
           (f 0)))]
      [(p v0 v1)
       (let ([len (vector-length v0)])
         (letrec ([f (lambda (n)
                       (if (= n len)
                           (void)
                           (begin
                             (p (vector-ref v0 n) (vector-ref v1 n))
                             (f (+ n 1)))))])
           (f 0)))]
      [(p v . rest)
       (let ([len (vector-length v)])
         (letrec ([f (lambda (n)
                       (if (= n len)
                           (void)
                           (begin
                             (apply p (vector-ref v n) (map (lambda (v) (vector-ref v n)) rest))
                             (f (+ n 1)))))])
           (f 0)))]))

  (define-library-entry vector-map
    (case-lambda
      [(p v)
       (let ([len (vector-length v)])
         (let ([v-out (make-vector len)])
           (letrec ([f (lambda (n)
                         (if (= n 0)
                             v-out
                             (let ([n (- n 1)])
                               (vector-set! v-out n (p (vector-ref v n)))
                               (f n))))])
             (f len))))]
       [(p v0 v1)
        (let ([len (vector-length v0)])
          (let ([v-out (make-vector len)])
            (letrec ([f (lambda (n)
                          (if (= n 0)
                              v-out
                              (let ([n (- n 1)])
                                (vector-set! v-out n (p (vector-ref v0 n) (vector-ref v1 n)))
                                (f n))))])
              (f len))))]
       [(p v . rest)
        (let ([len (vector-length v)])
          (let ([v-out (make-vector len)])
            (letrec ([f (lambda (n)
                          (if (= n 0)
                              v-out
                              (let ([n (- n 1)])
                                (vector-set! v-out n
                                  (apply p (vector-ref v n)
                                    (map (lambda (v) (vector-ref v n)) rest)))
                                (f n))))])
              (f n))))]))

  (define-library-entry zero?
    (lambda (n)
      (= n 0)))
    
)

;;; match.ss: a simple pattern matcher in scheme
;;;
;;; Copyright Andy Keep
;;; Licensed under the CRAPL: http://matt.might.net/articles/crapl/
;;;
;;; I've used or written variations on this kind of a match syntax
;;; for a long time now and finally decided to pull together one of
;;; my own.  It matches some in syntax and probably inadvertantly
;;; steals some of the design pattern (in this case the success and
;;; failure continuations, but was written from scratch and could
;;; almost certainly use improvement.
;;;
;;; Syntax:
;;; (match <exp> <cl> ...)
;;;
;;; where <cl> is:
;;;
;;; <cl> => [<pat> (guard <exp> ... <exp>) <exp> ... <exp>]
;;;         [<pat> <exp> ... <exp>]
;;;         [else <exp> ... <exp>]
;;;
;;; where the "else" clause may only appear as the last clause.  The guarded
;;; pattern matches when <pat> matches and all of the <exp> in
;;; (guard <exp> ...  <exp>) evaluate to true (<exp> in guard are effectively
;;; treated as an and).  The unguarded pattern matches when <pat> is matched,
;;; and the else clause matches when all else fails.  Clauses are evaluated in
;;; order, from first to last, with the else clause executed when all other
;;; clauses are exhausted.  If no else clause exists, match will raise an error
;;; to indicate it failed to find a suitable match.
;;;
;;; where <pat> is of the form:
;;; <pat> => sym                 -- matches symbol exactly
;;;          (<pat>0 . <pat>1)   -- matches a pair with <pat>0 as car and <pat>1 as cdr
;;;          (<pat> ...)         -- matches 0 or more <pat>
;;;          (<pat>0 ... <pat>1) -- matches 0 or more <pat>0 followed by a <pat>1
;;;          ,id                 -- binds id to the current expression
;;;
;;; examples:
;;;
;;; (match e
;;;   [(lambda (,x) ,body) (guard (symbol? x)) ---]
;;;   [(,e0 ,e1) ---]
;;;   [,x (guard (symbol? x)) ---])
;;;
;;; matches the terms of the lambda calculus and
;;;
;;; (match e
;;;   [(lambda (,x* ...) ,body* ... ,body) (guard (andmap symbol? x*)) ---]
;;;   [(let ([,x* ,e*] ...) ,body* ... ,body) (guard (andmap symbol? x*)) ---]
;;;   [(letrec ([,x* ,e*] ...) ,body* ... ,body) (guard (andmap symbol? x*)) ---]
;;;   [(if ,e0 ,e1 ,e2) ---]
;;;   [(,e ,e* ...) ---]
;;;   [,x (guard (symbol? x)) ---]
;;;   [else ---])
;;;
;;; matches a subset of scheme.
;;;

(library (match)
  (export match)
  (import (rnrs) (only (chezscheme) datum errorf trace-define trace-define-syntax))
  (define-syntax xmatch
    (lambda (x)
      (define (extract-bindings pat)
        (let f ([pat pat] [bindings '()])
          (syntax-case pat (unquote)
            [,bind (identifier? #'bind) (cons #'bind bindings)]
            [(?a . ?d) (f #'?a (f #'?d bindings))]
            [_ bindings])))
      (define build-call-exp
        (case-lambda
          [(level proc bind-in args)
           (let f ([level level] [bind-in bind-in])
             (if (fx=? level 0)
                 #`(#,proc #,bind-in #,@args)
                 #`(map (lambda (t) #,(f (fx- level 1) #'t)) #,bind-in)))]
          [(level proc bind-in args extra-rvs)
           (if (fx=? level 0)
               #`(#,proc #,bind-in #,@args)
               (let f ([level level] [bind-in bind-in])
                 (with-syntax ([(ts* ...) (generate-temporaries (cons 'x extra-rvs))]
                               [(ts ...) (generate-temporaries (cons 'x extra-rvs))])
                   #`(let mv-map ([t bind-in])
                       (values #,@(map (lambda (x) #''()) (cons 'x extra-rvs)))
                       (let-values ([(ts* ...) (mv-map (cdr t))]
                                    [(ts ...) #,(if (fx=? level 1)
                                                    #`(#,proc (car t) #,@args)
                                                    #`(let ([t (car t)])
                                                        #,(f (fx- level 1) #'t)))])
                         (values (cons ts ts*) ...))))))]))
      (define (process-pattern id level pat body fk)
        (with-syntax ([id id] [fk fk])
          (syntax-case pat (unquote)
            [,?bind (identifier? #'?bind) #`(let ([?bind id]) #,body)]
            [(?a dots)
             (eq? (datum dots) '...)
             (with-syntax ([(binding ...) (extract-bindings #'?a)]
                           [(t0 t1 loop) (generate-temporaries '(t0 t1 loop))])
               (with-syntax ([(tbinding ...) (generate-temporaries #'(binding ...))])
                 #`(let loop ([t0 id] [tbinding '()] ...)
                     (cond
                       [(pair? t0)
                        (let ([t1 (car t0)] [t0 (cdr t0)])
                          #,(process-pattern #'t1 (fx+ level 1) #'?a
                               #'(loop t0 (cons binding tbinding) ...)
                               #'fk))]
                       [(null? t0)
                        (let ([binding (reverse tbinding)] ...)
                          #,body)]
                       [else (fk)]))))]
            [(?a dots . ?d)
             (eq? (datum dots) '...)
             (with-syntax ([(binding ...) (extract-bindings #'?a)]
                           [(t0 t1 new-fk loop) (generate-temporaries '(t0 t1 new-fk loop))])
               (with-syntax ([(tbinding ...) (generate-temporaries #'(binding ...))])
                 #`(let loop ([t0 id] [tbinding '()] ...)
                     (let ([new-fk (lambda ()
                                     (if (pair? t0)
                                         (let ([t1 (car t0)] [t0 (cdr t0)])
                                           #,(process-pattern #'t1 (fx+ level 1) #'?a
                                               #'(loop t0 (cons binding tbinding) ...)
                                               #'fk))
                                         (fk)))])
                       #,(process-pattern #'t0 level #'?d
                           #`(let ([binding (reverse tbinding)] ...)
                               #,body)
                           #'new-fk)))))]
            [(?a . ?d)
             (with-syntax ([(a d) (generate-temporaries '(a d))])
               #`(if (pair? id)
                     (let ([a (car id)] [d (cdr id)])
                       #,(process-pattern #'a level #'?a
                           (process-pattern #'d level #'?d body #'fk)
                           #'fk))
                     (fk)))]
            [under (eq? (datum under) '_) body]
            [sym (identifier? #'sym) #`(if (eq? id 'sym) #,body (fk))]
            [() #`(if (null? id) #,body (fk))])))
      (define (process-clause id cl fk)
        (syntax-case cl (guard)
          [[pat (guard e0 e1 ...) body0 body1 ...]
           (process-pattern id 0 #'pat
             #`(if (and e0 e1 ...)
                   (begin body0 body1 ...)
                   (#,fk))
             fk)]
          [[pat body0 body1 ...]
           (process-pattern id 0 #'pat #'(begin body0 body1 ...) fk)]))
      (define (process-match id cl* else-body)
        (let f ([cl* cl*])
          (if (null? cl*)
              else-body
              (let ([cl (car cl*)] [cl* (cdr cl*)])
                (with-syntax ([(fk) (generate-temporaries '(fk))])
                  #`(let ([fk (lambda () #,(f cl*))])
                      #,(process-clause id cl #'fk)))))))
      (syntax-case x (else)
        [(_ id cl ... [else ebody0 ebody1 ...])
         (identifier? #'id)
         (with-syntax ([body (process-match #'id #'(cl ...) #'(begin ebody0 ebody1 ...))])
           #`(let f ([id id]) body))]
        [(_ id cl ...)
         (identifier? #'id)
         #'(xmatch id
             cl ...
             [else (errorf 'match "~s does not match any clauses" id)])]
        [(_ e cl ... [else ebody0 ebody1 ...])
         #'(let ([t e]) (xmatch t cl ... [else ebody0 ebody1 ...]))]
        [(_ e cl ...)
         #'(let ([t e])
             (xmatch t
               cl ...
               [else (errorf 'match "~s does not match any clauses" t)]))])))
  
  (define-syntax match
    (lambda (x)
      (define (process-cata cata level body)
        (define (serror) (syntax-violation 'match "invalid cata syntax" x cata))
        (define (s0 cata)
          (syntax-case cata ()
            [[colon . rest] (eq? (datum colon) ':) (s2 #'matcher #'rest)]
            [[arrow . rest] (eq? (datum arrow) '->) (s4 #'matcher (generate-temporaries '(in-id)) '() #'rest)]
            [[e . rest] (s1 #'e #'rest)]
            [[] (finish #'matcher (generate-temporaries '(in-id)) (list))]
            [_ (serror)]))
        (define (s1 e cata)
          (syntax-case cata ()
            [[colon . rest] (eq? (datum colon) ':) (s2 e #'rest)]
            [[arrow . rest]
             (and (eq? (datum arrow) '->) (identifier? e))
             (s4 #'matcher (list e) '() #'rest)]
            [[expr . rest]
             (identifier? e)
             (s3 #'matcher (list e) #'rest)]
            [[] (identifier? e) (finish #'matcher (generate-temporaries '(in-id)) (list e))]
            [_ (serror)]))
        (define (s2 f cata)
          (syntax-case cata ()
            [[arrow . rest] (eq? (datum arrow) '->) (s4 f (generate-temporaries '(in-id)) '() #'rest)]
            [[id . rest] (identifier? #'id) (s3 f (list #'id) #'rest)]
            [_ (serror)]))
        (define (s3 f e* cata)
          (syntax-case cata ()
            [[arrow . rest] (eq? (datum arrow) '->) (s4 f (reverse e*) '() #'rest)]
            [[e . rest] (s3 f (cons #'e e*) #'rest)]
            [[] (for-all identifier? e*) (finish f (generate-temporaries '(in-id)) (reverse e*))]))
        (define (s4 f in-id-arg* out-id* cata)
          (syntax-case cata ()
            [[id . rest] (identifier? #'id) (s4 f in-id-arg* (cons #'id out-id*) #'rest)]
            [[] (finish f in-id-arg* (reverse out-id*))]
            [_ (serror)]))
        (define (finish f in-id-arg* out-id*)
          (if (fx=? (length out-id*) 1)
              (finish-sv f in-id-arg* (car out-id*))
              (finish-mv f in-id-arg* out-id*)))
        (define (finish-sv f in-id-arg* out-id)
          (with-syntax ([call-expr
                         (if (fx=? (length in-id-arg*) 1)
                             (finish-sv-in-sv-out f (car in-id-arg*))
                             (finish-mv-in-sv-out f in-id-arg*))])
            #`(#,(car in-id-arg*) (let ([#,out-id call-expr]) #,body))))
        (define (finish-mv f in-id-arg* out-id*)
          (with-syntax ([call-expr
                         (if (fx=? (length in-id-arg*) 1)
                             (finish-sv-in-mv-out f (car in-id-arg*) out-id*)
                             (finish-mv-in-mv-out f in-id-arg* out-id*))])
            #`(#,(car in-id-arg*) (let-values ([#,out-id* call-expr]) #,body))))
        (define (finish-sv-in-sv-out f in-id)
          (if (fx=? level 0)
              #`(#,f #,in-id)
              (let loop ([level level] [in-id in-id])
                (if (fx=? level 1)
                    #`(map #,f #,in-id)
                    #`(map (lambda (t) #,(loop (fx- level 1) #'t)) #,in-id)))))
        (define (finish-mv-in-sv-out f in-id-arg*)
          (with-syntax ([(id arg* ...) in-id-arg*])
            (let loop ([level level] [in-id #'id])
              (if (fx=? level 0)
                  #`(#,f #,in-id arg* ...)
                  #`(map (lambda (t) #,(loop (fx- level 1) #'t)) #,in-id)))))
        (define (finish-sv-in-mv-out f in-id out-id*)
          (if (fx=? level 0)
              #`(#,f #,in-id)
              (with-syntax ([(ts* ...) (generate-temporaries out-id*)]
                            [(ts ...) (generate-temporaries out-id*)]
                            [(end ...) (map (lambda (ignore) #''()) out-id*)])
                (let loop ([level level] [in-id in-id])
                  (if (fx=? level 1)
                      #`(let mv-map ([t #,in-id])
                          (if (null? t)
                              (values end ...)
                              (let-values ([(ts* ...) (mv-map (cdr t))]
                                           [(ts ...) (f (car t))])
                                (values (cons ts ts*) ...))))
                      #`(let mv-map ([t #,in-id])
                          (if (null? t)
                              (values end ...)
                              (let-values ([(ts* ...) (mv-map (cdr t))]
                                           [(ts ...) #,(loop (fx- level 1) #`(car #,in-id))])
                                (values (cons ts ts*) ...)))))))))
        (define (finish-mv-in-mv-out f in-id-arg* out-id*)
          (with-syntax ([(id arg* ...) in-id-arg*]
                        [(ts* ...) (generate-temporaries out-id*)]
                        [(ts ...) (generate-temporaries out-id*)]
                        [(end ...) (map (lambda (ignore) #''()) out-id*)])
            (let loop ([level level] [in-id #'id])
              (if (fx=? level 0)
                  #`(#,f #,in-id arg* ...)
                  #`(let mv-map ([t #,in-id])
                      (if (null? t)
                          (values end ...)
                          (let-values ([(ts* ...) (mv-map (cdr t))]
                                       [(ts ...) #,(loop (fx- level 1) #`(car #,in-id))])
                            (values (cons ts ts*) ...))))))))
        (s0 cata))
      (define (realize-catas pat body)
        (let loop ([pat pat] [level 0] [body body])
          (syntax-case pat (unquote)
            [,?bind (identifier? #'?bind) #`(#,pat #,body)]
            [,?cata
             (with-syntax ([(?bind body) (process-cata #'?cata level body)])
               #'(,?bind body))]
            [(?a dots)
             (eq? (datum dots) '...)
             (with-syntax ([(?a body) (loop #'?a (fx+ level 1) body)])
               #`((?a dots) body))]
            [(?a dots . ?d)
             (eq? (datum dots) '...)
             (with-syntax ([(?d body) (loop #'?d level body)])
               (with-syntax ([(?a body) (loop #'?a (fx+ level 1) #'body)])
                 #`((?a dots . ?d) body)))]
            [(?a . ?d)
             (with-syntax ([(?d body) (loop #'?d level body)])
               (with-syntax ([(?a body) (loop #'?a level #'body)])
                 #`((?a . ?d) body)))]
            [under (eq? (datum under) '_) #`(#,pat #,body)]
            [sym (identifier? #'sym) #`(#,pat #,body)]
            [() #`(#,pat #,body)])))
      (define (process-clause cl)
        (syntax-case cl (guard)
          [[pat (guard ge0 ge1 ...) body0 body1 ...]
           (with-syntax ([(pat body) (realize-catas #'pat #'(let () body0 body1 ...))])
             #'[pat (guard ge0 ge1 ...) body])]
          [[pat body0 body1 ...]
           (with-syntax ([(pat body) (realize-catas #'pat #'(let () body0 body1 ...))])
             #'[pat body])]))
      (syntax-case x (else)
        [(_ id cl ... [else e0 e1 ...])
         (identifier? #'id)
         (with-syntax ([(cl ...) (map process-clause #'(cl ...))])
           #'(let matcher ([id id])
               (xmatch id cl ... [else e0 e1 ...])))]
        [(_ id cl ...)
         (identifier? #'id)
         (with-syntax ([(cl ...) (map process-clause #'(cl ...))])
           #'(let matcher ([id id])
               (xmatch id cl ...)))]
        [(_ expr cl ... [else e0 e1 ...])
         (with-syntax ([(cl ...) (map process-clause #'(cl ...))])
           #'(let matcher ([t expr])
               (xmatch t cl ... [else e0 e1 ...])))]
        [(_ expr cl ...)
         (with-syntax ([(cl ...) (map process-clause #'(cl ...))])
           #'(let matcher ([t expr])
               (xmatch t cl ...)))]))))

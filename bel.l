; (define-global cons (a b) (if (nil? b) (list a) (obj? b) `(,a ,@b) `(,a rest: ,b)))
; (define-global car (x) (if (nil? x) x (hd x)))
; (define-global cdr (x) (if (nil? x) x (tl x)))


(during-compilation

(define-global bel-t 't)
(define-global bel-o 'o)
(define-global bel-nil 'nil)

(define-global bel-err (kind)
  ;(print (str `(bel-err ,(if (obj? kind) (get kind 'message) kind))))
  (print (str `(bel-err ,kind)))
  ;(if (obj? kind) (throw kind) (error kind))
  ;(error kind)
  )

(define-global bel-false? (x)
  (= x false))

(define-global bel-nil? (x)
  (or (nil? x)
      (= x bel-nil)
      (and (obj? x) (none? x))))

(define-global bel-no (x)
  (or (bel-false? x)
      (bel-nil? x)))

(define-global bel-yes (x)
  (not (bel-no x)))

(define-global bel-id (a b)
  (when (or (= a b)
            (and (bel-no a) (bel-no b)))
    bel-t))

(define-global bel-prn (label x)
  (print (cat "TKTK: " (str label) " " (str x)))
  x)

(define-global bel-join (a b)
  (if (bel-nil? b) (if (bel-nil? a) (list) (list a))
      (obj? b) `(,a ,@b)
    `(,a rest: ,b)))

(define-global bel-car (x)
  (if (nil? x) x (hd x)))

(define-global bel-cdr (x)
  (if (nil? x) x (let r (tl x)
                   (if (and (has? r 'rest)
                            (none? r))
                       (get r 'rest)
                      r))))

(define-global bel-uvar ((o name 'u))
  (unique (cat "bel-" name)))
)

(during-compilation
  (define-macro bel-let (lh rh ...)
    `(let (,lh ,rh)
       ,@(list ...)))

  (define-macro bel-eif (v expr fail then)
    (let-unique (ok)
      `(let ((,ok ,v) (guard ,expr))
         (if ,ok ,then ,fail))))
  
  (define-macro bel-case (expr ...)
    (let args (list ...)
      (if (bel-no (bel-cdr args))
          (bel-car args)
          (let v (bel-uvar 'v)
            `(let ,v ,expr
               (if (= ,v ',(bel-car args))
                   ,(bel-car (bel-cdr args))
                   (bel-case ,v ,@(bel-cdr (bel-cdr args)))))))))

  (define-macro bel-iflet (var ...)
    (let args (list ...)
      (if (bel-no (bel-cdr args))
          (bel-car args)
          (let v (bel-uvar 'v)
            `(let ,v ,(bel-car args)
               (if (bel-yes ,v)
                   (let (,var ,v) ,(bel-car (bel-cdr args)))
                   (bel-iflet ,var ,@(bel-cdr (bel-cdr args)))))))))

  (define-macro bel-aif (...)
    `(bel-iflet it ,@(list ...)))
)


(during-compilation

(define-global bel-atom (x)
  (bel-no (bel-id (bel-type x) 'pair)))

(define-global bel-all (f xs)
  (if (bel-no xs)      bel-t
      (f (bel-car xs)) (bel-all f (bel-cdr xs))
      nil))

(define-global bel-some (f xs)
  (if (bel-no xs)      nil
      (f (bel-car xs)) xs
    (bel-some f (bel-cdr xs))))

(define-global bel-type (x)
  (if (bel-nil? x) 'symbol
      (obj? x) 'pair
      (string-literal? x) 'char
      (number? x) 'number
      (string? x) 'symbol
      (function? x) 'function
    (error (cat "bel-type: unknown " (str x)))))

(define-global bel-reduce (f xs)
  (if (bel-no (bel-cdr xs))
      (bel-car xs)
      (f (bel-car xs) (bel-reduce f (bel-cdr xs)))))

(define-global bel-cons ((o a bel-nil) (o b bel-nil) ...)
  (bel-reduce bel-join (list a b ...)))

(define-global bel-apply (f args ...)
  (if (> (target lua: (select "#" ...) js: (# (list ...))) 0)
      (apply f (bel-cons args ...))
    (apply f args)))

(define-global bel-append (...)
  (let args (list ...)
    (if (bel-no (bel-cdr args)) (bel-car args)
        (bel-no (bel-car args)) (bel-apply bel-append (bel-cdr args))
      (bel-cons (bel-car (bel-car args))
                (bel-apply bel-append
                           (bel-cdr (bel-car args))
                           (bel-cdr args))))))

(define-global bel-snoc (...)
  (let args (list ...)
    (bel-append (bel-car args) (bel-cdr args))))

(define-global bel-list (...)
  (bel-append (list ...) bel-nil))

(define-global bel-map (f ...)
  (let ls (list ...)
    (if (bel-no ls)          nil
        (bel-some bel-no ls) nil
        (bel-no (bel-cdr ls)) (bel-cons (f (bel-car (bel-car ls)))
                                        (bel-map f (bel-cdr (bel-car ls))))
      (bel-cons (bel-apply f (bel-map bel-car ls))
                (bel-apply bel-map f (bel-map bel-cdr ls))))))

(define-global bel-= (...)
  (let args (list ...)
    (if (bel-no (bel-cdr args))  bel-t
        (bel-some bel-atom args) (bel-all (fn (_) (bel-id _ (bel-car args))) (bel-cdr args))
      (and (bel-apply bel-= (bel-map bel-car args))
           (bel-apply bel-= (bel-map bel-cdr args))))))

(define-global bel-find (f xs)
  (bel-aif (bel-some f xs) (bel-car it)))

(define-global bel-begins (xs pat (o f bel-=))
  (if (bel-no pat)                   bel-t
      (bel-atom xs)                  nil
      (f (bel-car xs) (bel-car pat)) (bel-begins (bel-cdr xs) (bel-cdr pat) f)
                                     nil))

(define-global bel-caris (x y (o f bel-=))
  (bel-begins x (bel-list y) f))

(define-global bel-symbol (x) (bel-= (bel-type x) 'symbol))

(define-global bel-pair   (x) (bel-= (bel-type x) 'pair))

(define-global bel-char   (x) (bel-= (bel-type x) 'char))

(define-global bel-stream (x) (bel-= (bel-type x) 'stream))

(define-global bel-proper (x)
  (or (bel-no x)
      (and (bel-pair x) (bel-proper (bel-cdr x)))))

(define-global bel-string (x)
  (and (bel-proper x) (bel-all bel-char x)))

(define-global bel-mem (x ys (o f bel-=))
  (bel-some (fn (_) (f _ x)) ys))

(define-global bel-in (x ...)
  (bel-mem x (list ...)))

(define-global bel-literal (e)
  (or ;(in e t nil o apply)
      (bel-in e bel-t bel-nil bel-o 'apply apply bel-apply)
      (bel-in (bel-type e) 'char 'stream 'number) ; notice we check number here, departing from bel
      (bel-caris e 'lit)
      (bel-string e)))

(define-global bel-vmark (bel-join 'vmark))

(define-global bel-variable (e)
  (if (bel-atom e)
      (bel-no (bel-literal e))
      (bel-id (bel-car e) bel-vmark)))

(define-global bel-isa (name)
  (fn (_) (bel-begins _ `(lit ,name) bel-id)))
)

(during-compilation

(define-global bel-keep (f xs)
  (if (bel-no xs)      nil
      (f (bel-car xs)) (bel-cons (bel-car xs) (bel-keep f (bel-cdr xs)))
    (bel-keep f (bel-cdr xs))))

(define-global bel-rem (x ys (o f bel-=))
  (bel-keep (fn (_) (bel-no (f _ x))) ys))

(define-global bel-get (k kvs (o f bel-=))
  (bel-find (fn (_) (f (bel-car _) k)) kvs))

(define-global bel-put (k v kvs (o f bel-=))
  (bel-cons (bel-cons k v)
            (bel-rem k kvs (fn (x y) (f (bel-car x) y)))))

(define-global bel-rev (xs)
  (if (bel-no xs)
      nil
      (bel-snoc (bel-rev (bel-cdr xs)) (bel-car xs))))

(define-global bel-snap (xs ys (o acc))
  (if (bel-no xs)
      (list acc ys)
      (bel-snap (bel-cdr xs) (bel-cdr ys) (bel-snoc acc (bel-car ys)))))

  
)

(define-global bel-sigerr ((o msg 'no-err) s r m)
  (print (str `(bel-sigerr :msg ,msg :s ,s :r ,r :m ,m)))
  (bel-err msg))

(define-global bel-applyprim (f args s r m)
  (let (a (bel-car args)
        b (bel-car (bel-cdr args))
        bad (bel-uvar 'bad))
    (bel-eif v (bel-case f
                  id (bel-id a b)
                  join (bel-join a b)
                  car (bel-car a)
                  cdr (bel-cdr a)
                  type (bel-type a)
                  prn (bel-prn b a)
                  bad)
             (bel-sigerr v s r m)
             (if (bel-id v bad)
                 (bel-sigerr 'unknown-prim s r m)
                 (bel-mev s (bel-cons v r) m)))))

(define-global bel-locked? (s)
  (print (str `(bel-locked? ,(bel-yes (bel-cdr (bel-binding 'lock s))))))
  (bel-yes (bel-cdr (bel-binding 'lock s))))

(define-global bel-mev ((o s bel-nil) (o r bel-nil) (o (p g) ()))
  (print (str `(bel-mev ,s ,r ,p ,g)))
  (if (bel-no s)
      (if (bel-yes p)
          (bel-sched p g)
          (bel-car r))
      (bel-sched (if (bel-locked? s)
                     (bel-cons (bel-list s r) p)
                     (bel-snoc p (bel-list s r)))
                 g)))

(define-global bel-sched (((s r) . p) g)
  (bel-ev s r (bel-list p g)))

(define-global bel-ev (((e a) . s) r m)
  (print (str `(bel-ev :e ,e :a ,a :s ,s :r ,r :m ,m)))
  (bel-aif (bel-literal e)            (bel-mev s (bel-cons e r) m)
           (bel-variable e)           (bel-vref e a s r m)
           (bel-no (bel-proper e))    (bel-sigerr 'malformed s r m)
           (bel-get (bel-car e) bel-forms bel-id) ((bel-cdr it) (bel-cdr e) a s r m)
    (bel-evcall e a s r m)))

(define-global bel-vref (v a s r m)
  (let g (bel-car (bel-cdr m))
    (if ; (inwhere s)
        ; (aif (or (lookup v a s g)
        ;          (and (car (inwhere s))
        ;               (let cell (cons v nil)
        ;                 (xdr g (cons cell (cdr g)))
        ;                 cell)))
        ;      (mev (cdr s) (cons (list it 'd) r) m)
        ;      (sigerr 'unbound s r m))
        (bel-aif (bel-lookup v a s g)
                 (bel-mev s (bel-cons (bel-cdr it) r) m)
                 (bel-sigerr (list 'unboundb v) s r m)))))

(define-global bel-smark (bel-join 'smark))

(during-compilation
  (define-macro bel-fu (...)
    (let args (list ...)
      `(list (list bel-smark 'fut (fn ,@args)) nil))))

(define-global bel-evmark (e a s r m)
  (print (str `(bel-evmark :e ,e :a ,a :s ,s :r ,r :m ,m)))
  (bel-case (bel-car e)
    fut  ((bel-car (bel-cdr e)) s r m)
    bind (bel-mev s r m)
    loc  (bel-sigerr 'unfindable s r m)
    prot (bel-mev (bel-cons (bel-list (bel-car (bel cdr e)) a)
                            (bel-fu (s r m) (bel-mev s (bel-cdr r) m))
                            s)
                  r
                  m)
    (bel-sigerr 'unknown-mark s r m)))

(define-global bel-forms (bel-list (bel-cons bel-smark bel-evmark)))

(during-compilation
(define-global bel-formfn (parms body)
  (let (v  (bel-uvar 'v)
        w  (bel-uvar 'w)
        ps (bel-parameters (bel-car parms)))
    ; (print (list "TKTK" v w ps parms))
    `(fn ,v
       (bel-eif ,w (bel-apply (fn ,(bel-car parms) (list ,@ps))
                              (bel-car ,v))
                (bel-apply bel-sigerr 'bad-form (bel-cdr (bel-cdr ,v)))
                (let (,ps ,w)
                  (let (,(bel-cdr parms) (bel-cdr ,v)) ,@body))))))

(define-global bel-parameters (p)
  (if (bel-no p)           nil
      (bel-variable p)     (list p)
      (bel-atom p)         (bel-err 'bad-parm)
      (bel-in (bel-car p) bel-t bel-o) (bel-parameters (bel-car (bel-cdr p)))
    (bel-append (bel-parameters (bel-car p))
                (bel-parameters (bel-cdr p)))))

(define-macro bel-form (name parms rest: body)
  `(set bel-forms (bel-put ',name ,(bel-formfn parms body) bel-forms)))

)

(bel-form quote ((e) a s r m)
  (bel-mev s (bel-cons e r) m))

(bel-form if (es a s r m)
  (print (str `(bel-if :es ,es :a ,a :s ,s :r ,r :m ,m)))
  (if (bel-no es)
      (bel-mev s (bel-cons nil r) m)
      (bel-mev (bel-cons (list (bel-car es) a)
                         (if (bel-yes (bel-cdr es))
                             (bel-cons (bel-fu (s r m)
                                         (bel-if2 (bel-cdr es) a s r m))
                                       s)
                             s))
               r
               m)))

(define-global bel-if2 (es a s r m)
  (print (str `(bel-if2 :es ,es :a ,a :s ,s :r ,r :m ,m)))
  (bel-mev (bel-cons (list (if (bel-car r)
                               (bel-car es)
                               (bel-cons 'if (bel-cdr es)))
                           a)
             s)
       (bel-cdr r)
       m))

(bel-form dyn ((v e1 e2) a s r m)
  (print (str `(dyn :v ,v :e1 ,e1 :e2 ,e2 :a ,a :s ,s :r ,r :m ,m)))
  (if (bel-variable v)
      (bel-mev (bel-cons (list e1 a)
                         (bel-fu (s r m) (bel-dyn2 v e2 a s r m))
                         s)
               r
               m)
      (bel-sigerr 'cannot-bind s r m)))

(define-global bel-dyn2 (v e2 a s r m)
  (print (str `(dyn2 :v ,v :e2 ,e2 :a ,a :s ,s :r ,r :m ,m)))
  (bel-mev (bel-cons (bel-list e2 a)
                     (bel-list (bel-list bel-smark 'bind (bel-cons v (bel-car r)))
                           nil)
                     s)
           (bel-cdr r)
           m))

; (define-global bel-dyn (var expr body)
;   (print (cat "TKTK: " (str label) " " (str x)))
;   x)

(bel-form ccc ((f) a s r m)
  (bel-mev (bel-cons (list (list f (list 'lit 'cont s r))
                           a)
                     s)
           r
           m))

(define-global bel-lookup (e a s g)
  (or (bel-binding e s)
      (bel-get e a bel-id)
      (bel-get e g bel-id)
      (bel-case e
        scope (bel-cons e a)
        globe (bel-cons e g))))

(define-global bel-caddr (x)
  (bel-car (bel-cdr (bel-cdr x))))

(define-global bel-binding (v s)
  (bel-get v
           (bel-map bel-caddr (bel-keep (fn (_) (bel-begins _ (list bel-smark 'bind) bel-id))
                                        (bel-map bel-car s)))
           bel-id))

(define-global bel-evcall (e a s r m)
  (print (str `(bel-evcall :e ,e :a ,a :s ,s :r ,r :m ,m)))
  (bel-mev (bel-cons (list (bel-car e) a)
                     (bel-fu (s r m)
                       (bel-evcall2 (bel-cdr e) a s r m))
                     s)
           r
           m))

(define-global bel-evcall2 (es a s (op . r) m)
  (print (str `(bel-evcall2 :es ,es :a ,a :s ,s :op ,op :r ,r :m ,m)))
  (if ((bel-isa 'mac) op)
      (bel-applym op es a s r m)
      (bel-mev (bel-append (bel-map (fn (_) (list _ a)) es)
                           (bel-cons (bel-fu (s r m)
                                       (print (str `(bel-evcall2-fu :es ,es :s ,s :r ,r :m ,m)))
                                       (let ((args r2) (bel-snap es r))
                                         (print (str `(bel-evcall2-fu2 :args ,args :r2 ,r2 :es ,es :s ,s :r ,r :m ,m)))
                                         (bel-applyf op (bel-rev args) a s r2 m)))
                                     s))
               r
               m)))

(define-global bel-applyf (f args a s r m)
  (print (str `(bel-applyf :f ,f :args ,args :a ,a :s ,s :r ,r :m ,m)))
  (if (= f 'apply)   (bel-applyf (bel-car args) (bel-reduce bel-join (bel-cdr args)) a s r m)
      (bel-caris f 'lit) (if (bel-proper f)
                             (bel-applylit f args a s r m)
                             (bel-sigerr 'bad-lit s r m))
      ; TKTK: call compiled functions directly?
      ; (function? f) xxx
    (bel-sigerr 'cannot-apply s r m)))

(define-global bel-applylit (f args a s r m)
  (let ((tag . rest) (bel-cdr f))
    (bel-case tag
      prim (bel-applyprim (bel-car rest) args s r m)
      cont (let (((o s2) (o r2) . extra) ret)
             ; TODO: okstack
             (bel-applycont s2 r2 args s r m))
      (bel-sigerr 'unapplyable s r m))))

(define-global bel-applycont (s2 r2 args s r m)
  (if (or (bel-no args) (bel-cdr args))
      (bel-sigerr 'wrong-no-args s r m)
      (bel-mev (bel-append (bel-keep (fn (_) (and (bel-protected _) (bel-no (bel-mem _ s2 id))))
                                     s)
                           s2)
               (bel-cons (bel-car args) r2)
               m)))

(define-global bel-protected (x)
  (bel-some (fn (_) (bel-begins (bel-car x) (list bel-smark _) id))
            '(bind prot)))

(define-global bel-globe
  (bel-put 'id '(lit prim id)
  (bel-put 'car '(lit prim car)
  (bel-put 'cdr '(lit prim cdr)
  (bel-put 'join '(lit prim join)
  (bel-put 'type '(lit prim type)
  (bel-put 'prn '(lit prim prn)
  )))))))

(define-global bel-bel (e (o g bel-globe))
  (bel-ev (list (list e bel-nil))
          bel-nil
          (list bel-nil g)))

; (bel-lookup 'scope (bel-put 'foo 42) '((+ 1 2)) (bel-put 'car 'bel-car))
; (bel-lookup 'globe (bel-put 'foo 42) '((+ 1 2)) (bel-put 'car 'bel-car))
; (bel-ev '(("a")))
; (bel-ev '((42)))
; not working: (bel-ev `(((,bel-smark bind foo 42)) ((join 1 2))) nil (list nil (bel-put 'join bel-join)))
; (bel-ev `(((,bel-smark bind foo 42)) ((join 1 2))) nil (list nil (bel-put 'join '(lit prim join))))
; (bel-bel '(id 1 1))
; (bel-bel '(dyn x 42 (join x (quote (a b)))))

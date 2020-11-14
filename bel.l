; (define-global cons (a b) (if (nil? b) (list a) (obj? b) `(,a ,@b) `(,a rest: ,b)))
; (define-global car (x) (if (nil? x) x (hd x)))
; (define-global cdr (x) (if (nil? x) x (tl x)))

(during-compilation

(define-global bel-t 't)
(define-global bel-nil 'nil)

(define-global bel-err (kind)
  (print (str `(bel-err ,(if (obj? kind) (get kind 'message) kind))))
  (if (obj? kind) (throw kind) (error kind)))

(define-global bel--false? (x)
  (= x false))

(define-global bel--nil? (x)
  (or (nil? x)
      (= x bel-nil)
      (and (obj? x) (none? x))))

(define-global bel-no (x)
  (or (bel--false? x)
      (bel--nil? x)))

(define-global bel-yes (x)
  (not (bel-no x)))

(define-global bel-id (a b)
  (or (= a b)
      (and (bel-no a) (bel-no b))))

(define-global bel-type (x)
  (if (bel--nil? x) 'sym
      (obj? x) 'pair
      (string-literal? x) 'str
      (number? x) 'num
      (string? x) 'sym
    (error "bel-type: unknown")))

(define-global bel-join (a b)
  (if (bel--nil? b) (if (bel--nil? a) (list) (list a))
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

(define-global bel-atom (x)
  (bel-no (bel-id (bel-type x) 'pair)))


(define-global bel-reduce (f xs)
  (if (bel-no (bel-cdr xs))
      (bel-car xs)
      (f (bel-car xs) (bel-reduce f (bel-cdr xs)))))

(define-global bel-cons ((o a bel-nil) (o b bel-nil) ...)
  (bel-reduce bel-join (list a b ...)))

(define-global bel-apply (f args ...)
  (if (> (select "#" ...) 0)
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

(define-global bel-uvar ((o name 'u))
  (unique (cat "bel-" name)))
)

(during-compilation
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

(define-global bel-sigerr ((o msg 'no-err) s r m)
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
                  bad)
             (bel-sigerr v s r m)
             (if (bel-id v bad)
                 (bel-sigerr 'unknown-prim s r m)
                 (bel-mev s (bel-cons v r) m)))))

(define-global bel-locked? (s)
  ;(cdr (binding 'lock s))
  bel-nil)

(define-global bel-mev ((o s 'nil) (o r 'nil) (o (p g) ()))
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
  (print (str `(bel-ev :e ,e :a ,a :s ,s :r ,r :m ,m))))

(define-global bel-applylit (f args a s r m)
  (let ((tag . rest) (bel-cdr f))
    (bel-case tag
      prim (bel-applyprim (bel-car rest) args s r m)
      (bel-sigerr 'unapplyable s r m))))

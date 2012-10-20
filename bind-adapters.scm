;;; This is a helper-module to bind which provides `adapters` and
;;; helper functions to manipulate foreign argument types.

;;; Bind adapters allow transforming foreign bindings (usually as foreign-lambda
;;; expressions) that the bind macros produce. It is useful for
;;; altering argument types.
;;;
;;; The default adapter will transform any foreign-lambda statements with a
;;; struct-by-value return-type.
(module bind-adapters (bind-adapt

                       add-adapter
                       remove-all-adapters

                       add-cexp-adapter
                       remove-all-cexp-adapters
                       reset-adapters

                       foreign-lambda-family?
                       foreign-lambda*-family?

                       transform

                       foreign-type-pointer-target
                       foreign-type-pointer?
                       foreign-type-struct-name
                       foreign-variable-type)

(import chicken scheme)
(use srfi-1 data-structures matchable)

(define (foreign-lambda-family? symbol)
  (memq symbol '(foreign-lambda foreign-safe-lambda)))

(define (foreign-lambda*-family? symbol)
  (memq symbol '(foreign-lambda* foreign-safe-lambda* foreign-primitive)))



;; outputs a string which could be used as a C variable name.
;; e.g. "unsigned-int" => "unsigned_int"
;; obs:
;; varnames starting with numbers pass!
(define (valid-C-varname s)
  (apply string (filter-map
                 (lambda (char)
                   (cond
                    ((char-whitespace? char) #\_)
                    ((char-alphabetic? char) char)
                    ((char-numeric? char) char)
                    ((eq? char #\-) #\_)
                    (else #f)))
                 (string->list s))))

;; cexp: an sexp with C semantics. used in foreign-lambda* instead of
;; flat strings. we are using this intermediate representation of
;; C-code so that we can manipulate it. it is very basic, but allows
;; us to do things like argument casting, return-type conversion and
;; similar things. (cexp->string '(= (deref "destination") ("vadd" v1
;; v2))) (cexp->string '("return" (+ (deref x) u)))
;;
;; this is the very small cexp code-generator:
(define (cexp->string cexp)
  (define (xpr->str cexp)
    (match cexp
      (('= var x) (conc (xpr->str var) " = " (xpr->str x)))
      (('* args ...) (conc (intersperse (map xpr->str args) "*")))
      (('+ args ...) (conc (intersperse (map xpr->str args) "+")))
      (('-> struct x) (conc (xpr->str struct) "->" (xpr->str x)))
      (('= var x) (conc (xpr->str var) " = " (xpr->str x)))
      (('deref x) (conc "*" (xpr->str x)))
      (((? string? str) args ...) (conc str (intersperse (map xpr->str args) ",")))
      ((? string? a) a)
      ((? symbol? a) (symbol->string a))
      ((? number? a) (number->string a))
      (else (error "invalid c-exp" cexp))))
  (match cexp
    (('stmt statements ...) (apply conc (map (cut conc <> ";\n") (map cexp->string statements))))
    (('return expr) (conc "return(" (xpr->str expr) ");"))
    (exp (xpr->str cexp))))

(define (cexp-expression? cexp)
  (case (car cexp)
    ((stmt return) #f)
    (else #t)))

;; some foreign-lambda* expressions contain cexp, convert this to C as a
;; last step (not processable after this, so should be last step)
(define (transform-compile-foreign-lambda* x)
  (match (strip-syntax x)
    (((? foreign-lambda*-family? fl) rtype args (? list? body))
     `(,fl ,rtype ,args
          ,(let ([c-code (cexp->string body)])
             (if (cexp-expression? body)
                 ;; add return(...) automatically
                 (if (not (eq? rtype 'void))
                     (conc "return(" c-code ");")
                     (conc c-code ";"))
                 c-code))))
    (else #f)))

;; stolen & modified from chicken-core's compiler.scm:
;; try to describe a foreign-lambda type specification
;; eg. (type->symbol '(c-pointer (struct "point"))) => point_ptr
;;     unsigned-int => unsigned_int
;; typically used to generate meaningful variable names
;; generated symbols are hopefully valid C var names
(define (argtype->symbol type-spec)
  (let loop ([type type-spec])
    (cond
     ((null? type) 'a)
     ((list? type)
      (case (car type)
        ((c-pointer) (string->symbol (conc (loop (cdr type)) "_ptr"))) ;; if pointer, append _ptr
        ((const struct) (loop (cdr type))) ;; ignore these
        (else (loop (car type)))))
     (else (string->symbol
            (valid-C-varname
             (if (symbol? type) (symbol->string type) type) ))))))


;; recursively transform any sexpr using transformer proc. sexpr is
;; replaced with return-value unless it is #f. obs: remember to strip
;; syntax!
(define (transform x transformer)
  (let loop ([x x])
    (let ([transformed (transformer x)])
      (or transformed
          (if (list? x)
              (map loop x)
              x)))))

;; find the name of the struct in argtype. 
;; (foreign-type-struct-name '(const (struct "point")))
;; (foreign-type-struct-name '(c-pointer (struct "point")))
;; (foreign-type-struct-name '(illagal (struct "point")))
(define (foreign-type-struct-name argtype)
  (let loop ((argtype argtype))
    (match argtype
      [('struct sname) sname]
      [('const x)  (loop x)]
      [('c-pointer x) (loop x)]
      [('nonnull-c-pointer x) (loop x)]
      [else #f])))

;; return foreign type which is pointed to, #f if not a pointer
;; todo: work with c-string's and friends
;; (foreign-type-pointer? '(const (c-pointer int)))
;; (foreign-type-pointer? '(const (c-pointer (struct "foo"))))
;; (foreign-type-pointer? '(const (struct "foo")))
(define (foreign-type-pointer-target argtype)
  (let loop ((argtype argtype))
    (match argtype
      [('nonnull-c-pointer r) r]
      [('c-pointer r) r]
      [('const r) (loop r)]
      [else #f])))

(define (foreign-type-pointer? argtype)
  (and (foreign-type-pointer-target argtype) #t))

;; (struct-by-val? '(struct "foo"))
;; (struct-by-val? '((const (struct "foo")) var1) )
;; (struct-by-val? '(c-pointer (struct "foo")))
;; (struct-by-val? '((c-pointer (struct "foo")) var2))
;; (struct-by-val? '(int "foo"))
(define (struct-by-val? argdef)
  (let ([argtype (if (and (list? argdef) (list? (car argdef)))
                     (car argdef)
                     argdef)])
    (and (foreign-type-struct-name argtype)
         (not (foreign-type-pointer? argtype))
         #t)))

(define (make-variable argtype #!optional (rename gensym))
  (rename (argtype->symbol argtype)))

;; (wrap-in-variable 'float) => float12345
;; (wrap-in-variable 'float 'var1) => (float var1)
;; convenience rename: there may be several arguments of same type
(define (wrap-in-variable argtype #!optional (variable #f) (var-rename gensym))
  (list argtype (or variable (var-rename (argtype->symbol argtype)))))



;; add a pointer to a argtype or argdef (with
;; or without varname)
;; (wrap-in-pointer '(const (struct "mystruct")))
;;     => (((c-pointer (const ... ))))
(define (wrap-in-pointer arg-def)
  (let loop ((arg-def arg-def))
    (match arg-def
      (('struct _) `(c-pointer ,arg-def))
      (('const ('struct _)) `(c-pointer ,arg-def))
      (else (if (list? arg-def)
                `(,(loop (car arg-def)) ,@(cdr arg-def))
                arg-def)))) )

;; (foreign-variable-type 'var2 '((float var2) ((const (struct "foo")) var1)))
(define (foreign-variable-type variable argdefs)
  (let ([found (rassoc (list variable) argdefs equal?)])
    (if found (car found) #f)))

;; make foreign-lambda into its foreign-lambda* equivalent (with cexp)
;; so that transform-struct-argtypes can handle it
(define (foreign-lambda->foreign-lambda* x)
  (match (strip-syntax x)
    (((? foreign-lambda-family? fl) rtype cfunc-name argtypes ...)
     (let* ([vars (map make-variable argtypes)]
            [argdefs (map wrap-in-variable argtypes vars)])
       `(,(string->symbol (conc fl "*")) ,rtype ,argdefs
             (,cfunc-name ,@vars))))
    (else #f)))


;; find argument which pass structs by value and dereference it in C.
(define transform-struct-argtypes
  (lambda (x)
    (match (strip-syntax x)
      ;; match foreign-lambda* where body is cexp, and make struct-by-val
      ;; argtypes into their pointer-equivalents, and dereference any
      ;; occurance of them in the cexp.
      (((? foreign-lambda*-family? fl) rtype argdefs (? list? body ...))

       ;; wrap any struct-by-val argument into its pointer equivalent
       (define (wrap-structs-in-pointer a)
         (if (struct-by-val? a) (wrap-in-pointer a) a))

       ;; find variables that reference anything in argdefs,
       ;; and if they are structs, dereference them (because we turned
       ;; them into pointers in wrapped-argdefs)
       (define (transform-struct-varrefs a)
         (if (and (symbol? a)
                  (struct-by-val? (foreign-variable-type a argdefs)))
             (list 'deref a) #f))

       (let ([wrapped-argdefs (map wrap-structs-in-pointer argdefs)])
         `(,fl ,rtype ,wrapped-argdefs
                           ;; transform our cexp code:
                           ,(transform body transform-struct-varrefs))))
      (else #f))))


;; check for struct-by-value rtype, then add destination argument in
;; first position instead. this also maps struct-by-val in arguments
(define (transform-struct-rtype x #!optional (rename-overwrite-func
                                              (lambda (f) (string->symbol (conc f "!")))))
  (match (strip-syntax x)
    (('define sfunc-name ((? foreign-lambda*-family? fl) rtype argdefs (? list? body ...)))
     ;; transform if return-type is a struct and if cexp is one simple expression
     (and (struct-by-val? rtype) (cexp-expression? body)
          (let ([vars (map (lambda (argdef) (cadr argdef)) argdefs)])
            `(begin
               (define ,(rename-overwrite-func sfunc-name)
                 (,fl void
                      ((,(wrap-in-pointer rtype) destination) ,@argdefs)
                      (= (deref "destination")
                         ,body)))
               (define (,sfunc-name ,@vars)
                 (let ((blob-location (location (make-blob
                                                 (foreign-value
                                                  ,(conc "sizeof" (flatten rtype)) ;; fix
                                                  int)))))
                   (,(rename-overwrite-func sfunc-name) blob-location ,@vars)
                   blob-location))))))
    ;; no match, skip & continue:
    (else #f)))

(define (default-adapters)
  (list transform-struct-rtype
        transform-struct-argtypes))

(define *adapter-list*
  (default-adapters))

(define (add-adapter adapter)
  (set! *adapter-list* (cons adapter *adapter-list*)))

(define (remove-all-adapters)
  (set! *adapter-list* '()))

(define (reset-adapters)
  (set! *adapter-list* (default-adapters)))


(define *cexp-adapters*
  (list transform-compile-foreign-lambda*))

(define (add-cexp-adapter adapter)
  (set! *cexp-adapters* (cons adapter *cexp-adapters*)))

(define (remove-all-cexp-adapters)
  (set! *cexp-adapters* '()))


;; called on every (emit ...) from bind-translator
(define (bind-adapt x)
  (fold (lambda (transformer result)
          (transform result transformer))
        x
        (append (list foreign-lambda->foreign-lambda*)
                *adapter-list*
                *cexp-adapters*)))

)

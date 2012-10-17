;;; Bind adapters allow transforming foreign bindings (usually as foreign-lambda
;;; expressions) that the bind macros produce. It is useful for
;;; altering argument types.
;;;
;;; The default adapter will transform any foreign-lambda statements with a
;;; struct-by-value return-type.

;; arg-def eg: (struct "point")
(define (struct-name arg-def)
  (let loop ((arg-def arg-def))
    (match arg-def
      [('struct sname) sname]
      [('const ('struct sname))  sname]
      [else (if (list? arg-def) (loop (car arg-def)) #f)])))

(define struct-by-val? struct-name)

; ((const (struct "mystruct")) name) -> (((c-pointer (const ... ))) name)
(define (wrap-in-pointer arg-def)
  (let loop ((arg-def arg-def))
    (match arg-def
      (('struct _) `(c-pointer ,arg-def))
      (('const ('struct _)) `(c-pointer ,arg-def))
      (else (if (list? arg-def)
                `(,(loop (car arg-def)) ,@(cdr arg-def))
                arg-def)))) )

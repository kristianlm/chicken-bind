;; ****************************************************88
;; simple test-suite for testing the struct-by-value features
;; of chicken-bind
;;
;; testing struct-by-val return-types,
;; argument types and nested structs
;; 

(import bind foreign)
(print "testing structs by value ..")


;; add renaming to ensure scheme variable names
;; don't end up in generated C-code wrappers.
(bind-options default-renaming: "vct:" mutable-fields: #f)
(bind-rename/pattern "vct-" "")

;; testing nested structs
(bind* "
typedef struct vct_point { float x, y ; }  vct_point ;
")

(define p1 (vct:make-point 1 2))
(define p2 (vct:make-point -1 -2))


;; testing struct-by-val in arguments
(bind* "
float vct_lensq(vct_point p) {
return pow(p.x, 2) +
       pow(p.y, 2);
};
float vct_len(vct_point p) {
return sqrt(vct_lensq(p));
}
")

(assert (= (vct:lensq p1) 5))
(assert (= (vct:lensq p2) 5))

;; testing struct-by-val return-type
(bind*
 "vct_point vct_normalize(vct_point p) {
float l = vct_len(p);
vct_point _p = { p.x / l, p.y / l};
return _p;
}")


(define (point->list p)
  (list (vct:point-x p) (vct:point-y p)))

(assert (and (= 1 (vct:len (vct:normalize p1)))
             (= 1 (vct:len (vct:normalize p2)))))

;; other misc testing

(bind*
"unsigned short point_equal(vct_point p, vct_point* pp) {
   if(&p == pp) return 2;
   if(p.x == pp->x && p.y == pp->y)
     return 1;

   return 0;
  }")

(assert (= 1 (vct:point-equal p1 p1)))
(assert (= 0 (vct:point-equal p1 p2)))

(assert (= 1 (vct:point-equal (vct:make-point 2 3) (vct:make-point 2 3))))
(assert (= 0 (vct:point-equal (vct:make-point 2 3) (vct:make-point 3 2))))

(print "struct-by-val tests done")

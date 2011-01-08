(use coops extras regex)
(import bind foreign)

(bind* #<<EOF

 struct My_struct { int x; ___mutable float y; };

 typedef struct My_struct My_struct;

 My_struct *make_struct(int x, float y) 
 {
   My_struct *s = (My_struct *)malloc(sizeof(My_struct));
   s->x = x;
   s->y = y;
   return s;
 }

EOF
)

(define s (make_struct 3 4))
(set! (My_struct-y s) 99)
(assert (equal? (list 3 99.0) (list (My_struct-x s) (My_struct-y s))))

;;================================================================================
;; Test number pattern

(bind #<<EOF

#define GLU_TESS_MAX_COORD 1.0e+150

#define X1_1 1.0e+150
#define X1_2 -1.0e+150
#define X1_3 -1.0e-150

#define X1_4 1.0E+150
#define X1_5 -1.0E+150
#define X1_6 -1.0E-150

#define X2_1 1.e150
#define X2_2 -1.e150
#define X2_3 -1.e-150
#define X2_4 1E+150
#define X2_5 -1e+150
#define X2_6 -1E-150

#define X3_1 1
#define X3_2 12
#define X3_3 -1
#define X3_4 -12

#define X4_1 1.
#define X4_2 12.
#define X4_3 -1.
#define X4_4 -12.

#define X5_1 1.0
#define X5_2 12.0
#define X5_3 -1.0
#define X5_4 -12.0
EOF
)

(assert (= -1.0 X5_3))

(bind-rename "foo" "bar")
(bind-rename/pattern "(.+)_(.+)_(.+)" "\\2")

(bind-options
 exception-handler: "abort();")

(bind-type "int32_t" char)

(bind* "int foo(___inout double *d) { return (int)*d; }")
(bind* "int32_t one_two_three(___inout double *d) { return (int)*d; }")

(assert (equal? '(22 22.3) (receive (bar 22.3))))
(two 22.5)
(assert (= #x16 (two 22.5)))

;;; ___out

 (bind* #<<EOF
 #ifndef CHICKEN
 #include <math.h>
 #endif

 double modf(double x, ___out double *iptr);
EOF
 )

 (let-values ([(frac int) (modf 33.44)])
   (print (list frac int)))

;;; ___length

 (require-extension srfi-4)

 (bind* #<<EOF
 double sumarray(double *arr, ___length(arr) int len)
 {
   double sum = 0;

   while(len--) sum += *(arr++);

   return sum;
 }
EOF
 )

 (assert (= (+ 33 44 55.66) (sumarray (f64vector 33 44 55.66))))

;;; 

#|
 (define mbstowcs (foreign-lambda int "mbstowcs" nonnull-u32vector c-string int))

 (define (str->ustr str)
   (let* ([len (string-length str)]
          [us (make-u32vector (add1 len) 0)] )
     (mbstowcs us str len)
     us) )

 (bind-type unicode nonnull-u32vector str->ustr)

 (bind* #<<EOF
 static void foo2(unicode ws)
 {
   printf("%ls\n", ws);
 }
EOF
 )

 (foo2 "this is a test!")
|#

;;;

 (bind-opaque-type myfile (c-pointer "FILE"))

 (bind "myfile fopen(char *, char *);")

(print (fopen "tests.scm" "r"))

;;;

 (bind-options prefix: "mylib:")

 (bind "#define SOME_CONST 42")

(assert (= 42 mylib:SOME_CONST))



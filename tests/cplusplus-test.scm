(use bind coops extras)
(use cplusplus-object)

(bind* #<<EOF

class Foo {
  char *name_;
public:
  Foo(char *name) { name_ = strdup(name); }
  ~Foo() {}
  char *name() { return name_; }
  Foo *bar(Foo *x) { return x; }
};

EOF
)

(define-method (print-object (x <Foo>) #!optional (out (current-output-port)))
  (fprintf out "#<Foo ~a>" (name x)))

(print "bind class")
(define x (new <Foo> "foo1"))
(pp x)
(pp (bar x (new <Foo> "foo2")))
(delete x)

;;;

(print "exception handler")

 (bind-options exception-handler: "catch(...) { return(0); }")

 (bind* #<<EOF
 class Foo2 {
  public:
   Foo2 *bar2(bool f) { if(f) throw 123; else return this; }
 };
EOF
 )

 (define f1 (new <Foo2>))
 
 (print (bar2 f1 #f))			; <Foo2>
 (print (slot-value f1 'this))
 (print (bar2 f1 #t))			; #f
 (delete f1)


;;;

(print "full specialization")

(use coops-primitive-objects)

 (bind-options full-specialization: #t)

 (bind* #<<EOF
 int overloaded(int x) { return x; }
 int overloaded(char *x) { return atoi(x); }
EOF
 )

 (bind-options full-specialization: #f)

(assert (= 1 (overloaded 1)))
(assert (= 2 (overloaded "2")))

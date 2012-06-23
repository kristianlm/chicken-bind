;;;; run.scm


(use setup-api)

(run (csc tests.scm -debug F -c++))
(run (./tests))

(run (csc struct-passing-tests.scm -debug F))
(run (./struct-passing-tests))

(run (csc cplusplus-test.scm -debug F -c++))
(run (./cplusplus-test))

;;;; run.scm


(use setup-api)

(run (csc tests.scm -debug F -c++))
(run (./tests))

(run (csc cplusplus-test.scm -debug F -c++))
(run (./cplusplus-test))

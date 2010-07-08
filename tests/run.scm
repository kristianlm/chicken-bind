;;;; run.scm


(run (csc tests.scm -debug F -c++))
(run (./tests))

(run (csc cplusplus-tests.scm -debug F -c++))
(run (./cplusplus-tests))

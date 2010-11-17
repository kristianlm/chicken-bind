;;;; runsilex.scm
;
; Runs silex and generates c.l.scm

(require-extension silex)

(lex "c.l" "c.l.scm" 'counters 'line)

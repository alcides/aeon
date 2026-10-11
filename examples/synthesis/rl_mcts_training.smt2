; Assertions describe a VALID formula, not just a satisfiable SMT instance.
; These equalities hold for all x,y. Anti-unification can replace selected
; additions with f calls, giving a synthesis task with an addition witness.
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (and (= (+ x 1) (+ 1 x)) (= (+ y 2) (+ 2 y))))

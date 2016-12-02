; benchmark generated from python API
(set-logic QF_UFLRA)
(set-info :status unknown)
(declare-fun y () Real)
(declare-fun x () Real)
(assert
 (> (+ x y) 5.0))
(assert
 (> x 1.0))
(assert
 (> y 1.0))
(check-sat)
(get-model)

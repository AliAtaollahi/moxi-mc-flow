; A clause with two predicates in its body is a derivation tree, not a path.
; horn2vmt reports `non-unary clause found` and the translation fails.
(set-logic HORN)
(declare-fun p (Int) Bool)
(declare-fun q (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (p x))))
(assert (forall ((x Int)) (=> (= x 1) (q x))))
(assert (forall ((x Int) (y Int)) (=> (and (p x) (q y)) false)))
(check-sat)

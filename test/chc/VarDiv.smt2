; Integer division by a variable. MathSAT has no Int division, so horn2vmt
; comes back with `to_int (/ (to_real x) (to_real y))`; `preprocess_vmt`
; restores `div`, splitting on the sign of the divisor.
(set-logic HORN)
(declare-fun inv (Int Int) Bool)
(assert (forall ((x Int) (y Int))
  (=> (and (= x 100) (> y 1)) (inv x y))))
(assert (forall ((x Int) (y Int) (x1 Int))
  (=> (and (inv x y) (> x 0) (= x1 (div x y))) (inv x1 y))))
(assert (forall ((x Int) (y Int))
  (=> (and (inv x y) (< x 0)) false)))
(check-sat)

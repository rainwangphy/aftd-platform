import AFTD.Prelude

/-!
# binary_four_parity_elimination

Topic: quantum   Node: 36348c52d2b2

Provenance: helper lemma. Supporting algebra for OP-3, arXiv:2610.01024, Section E.1; developed in deep session IN-184. These helpers do not establish a lower bound for arbitrary circuit gate lists.

For binary a,b,u,l, the sum of the four lifts u,u+a,u+b,u+a+b minus twice the lift of a*b+l equals (2+4*lift(a*b+l))*lift(u+l)+2*lift(a+b+u), modulo eight.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 50000000

theorem binary_four_parity_elimination (a b u l : ZMod 2) :
    ((u.val : ZMod 8) + ((u+a).val : ZMod 8) +
      ((u+b).val : ZMod 8) + ((u+a+b).val : ZMod 8)) -
        2 * ((a*b+l).val : ZMod 8) =
      (2 + 4 * ((a*b+l).val : ZMod 8)) * ((u+l).val : ZMod 8) +
        2 * ((a+b+u).val : ZMod 8) := by
  revert a b u l
  decide

import AFTD.Prelude

/-!
# op1957_zero_defect_relaxation_forbidden

Topic: graphs   Node: 97761fec9c23

Provenance: helper lemma. OP-1957: k=9 zero-defect relaxation, experiment 38245.

The ordered forbidden pairs of the explicit 36-vertex graph from the zero-defect relaxation.
-/

def op1957_zero_defect_relaxation_forbidden (u v : Fin 36) : Prop :=
  (u.val < 7 ∧ 7 ≤ v.val ∧ v.val < 18) ∨
  (18 ≤ u.val ∧ u.val < 25 ∧ 25 ≤ v.val) ∨
  ((7 ≤ u.val ∧ u.val ≤ 10 ∨ 25 ≤ u.val ∧ u.val ≤ 28) ∧
   (7 ≤ v.val ∧ v.val ≤ 10 ∨ 25 ≤ v.val ∧ v.val ≤ 28)) ∨
  (u.val = 0 ∧ 25 ≤ v.val ∧ v.val ≤ 28) ∨
  (u.val = 18 ∧ 7 ≤ v.val ∧ v.val ≤ 10) ∨
  (11 ≤ u.val ∧ u.val ≤ 13 ∧ 14 ≤ v.val ∧ v.val ≤ 17) ∨
  (11 ≤ u.val ∧ u.val ≤ 17 ∧ 32 ≤ v.val)

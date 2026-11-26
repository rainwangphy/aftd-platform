import AFTD.Prelude

/-!
# op1957_barrier_count_example_forbidden

Topic: graphs   Node: 2ffecdadc78d

Provenance: helper lemma. OP-1957; explicit graph from the saturated barrier count model, experiments 39772, 39775 and 39778.

The ordered forbidden vertex pairs defining the explicit 44-vertex barrier count example.
-/

def op1957_barrier_count_example_forbidden (u v : Fin 44) : Prop := (u.val < 5 ∧ 5 ≤ v.val ∧ v.val < 22) ∨
  (22 ≤ u.val ∧ u.val < 33 ∧ 33 ≤ v.val) ∨
  (u.val = 0 ∧ (v.val = 22 ∨ v.val = 23)) ∨
  (5 ≤ u.val ∧ u.val < 12 ∧ 33 ≤ v.val ∧ v.val < 37) ∨
  (5 ≤ u.val ∧ u.val < 12 ∧ (v.val = 22 ∨ v.val = 23 ∨ v.val = 24)) ∨
  (5 ≤ u.val ∧ u.val < 12 ∧ 5 ≤ v.val ∧ v.val < 12)

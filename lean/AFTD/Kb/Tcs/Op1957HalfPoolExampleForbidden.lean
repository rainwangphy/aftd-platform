import AFTD.Prelude

/-!
# op1957_half_pool_example_forbidden

Topic: graphs   Node: fea714d1a7c1

Provenance: helper lemma. OP-1957; explicit 52-vertex half-pool graph, experiments 39914, 39920, and 39925.

The ordered forbidden pairs for the 52-vertex half-pool example.
-/

def op1957_half_pool_example_forbidden (u v : Fin 52) : Prop :=(u.val < 5 ∧ 5 ≤ v.val ∧ v.val < 26) ∨
  (26 ≤ u.val ∧ u.val < 39 ∧ 39 ≤ v.val) ∨
  (u.val = 0 ∧ (v.val = 26 ∨ v.val = 27)) ∨
  ((u.val = 0 ∨ (5 ≤ u.val ∧ u.val < 8) ∨ (39 ≤ u.val ∧ u.val < 42)) ∧
    12 ≤ v.val ∧ v.val < 18) ∨
  (((8 ≤ u.val ∧ u.val < 12) ∨ u.val = 26 ∨ u.val = 27 ∨ u.val = 28) ∧
    12 ≤ v.val ∧ v.val < 18) ∨
  (12 ≤ u.val ∧ u.val < 18 ∧ 12 ≤ v.val ∧ v.val < 18) ∨
  ((u.val = 0 ∨ (5 ≤ u.val ∧ u.val < 8) ∨ (39 ≤ u.val ∧ u.val < 42)) ∧
    ((8 ≤ v.val ∧ v.val < 12) ∨ v.val = 26 ∨ v.val = 27 ∨ v.val = 28) ∧
    ¬ (u.val=0 ∧ v.val=28))

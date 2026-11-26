import AFTD.Prelude

/-!
# op1957_empty_pool_control_forbidden

Topic: graphs   Node: f1156bdfc691

Provenance: helper lemma. OP-1957; explicit exceptional empty-pool controls, experiments 41527, 41538 and 41541.

Ordered forbidden pairs in the two finite control graphs; z chooses the extra first-shore vertex.
-/

def op1957_empty_pool_control_forbidden (z u v : Fin 28) : Prop := (u.val < 5 ∧ 5 ≤ v.val ∧ v.val < 14) ∨
  (14 ≤ u.val ∧ u.val < 21 ∧ 21 ≤ v.val) ∨
  ((u.val = 0 ∨ u = z ∨ 21 ≤ u.val) ∧ (v.val = 14 ∨ v.val = 15 ∨ v.val = 16) ∧ ¬ (u.val = 0 ∧ v.val = 16)) ∨
  (u.val = 16 ∧ (v.val = 14 ∨ v.val = 15)) ∨ (u.val = 14 ∧ v.val = 15)

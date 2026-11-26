import AFTD.Prelude

/-!
# op1957_exceptional_pool_example_forbidden

Topic: graphs   Node: 239554004e49

Provenance: helper lemma. OP-1957; exceptional 44-vertex graph, experiments 40070–40073.

The ordered forbidden pairs for the exceptional 44-vertex graph.
-/

def op1957_exceptional_pool_example_forbidden (u v : Fin 44) : Prop :=(u.val < 5 ∧ 5 ≤ v.val ∧ v.val < 22) ∨
  (22 ≤ u.val ∧ u.val < 33 ∧ 33 ≤ v.val) ∨
  ((u.val=0 ∨ u.val=5 ∨ (33 ≤ u.val ∧ u.val < 40)) ∧
    (v.val=22 ∨ v.val=23 ∨ v.val=24) ∧ ¬ (u.val=0 ∧ v.val=24)) ∨
  ((u.val=22 ∨ u.val=23 ∨ u.val=24) ∧ (v.val=22 ∨ v.val=23 ∨ v.val=24)) ∨
  ((u.val=0 ∨ u.val=5 ∨ (33 ≤ u.val ∧ u.val < 40) ∨ u.val=22 ∨ u.val=23 ∨ u.val=24) ∧
    6 ≤ v.val ∧ v.val < 10) ∨
  (6 ≤ u.val ∧ u.val < 10 ∧ 6 ≤ v.val ∧ v.val < 10)

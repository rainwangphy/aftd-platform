import AFTD.Prelude

/-!
# subdivided_claw_rel

Topic: combinatorial_games   Node: 942c5df65561

Provenance: formalization of a published result. Source: arXiv:2611.32746 Prop 2.3, arXiv:2609.37796 Sec 3.1

Binary relation on Fin 7 for the once-subdivided claw with center 0 and branches 0-1-4, 0-2-5, 0-3-6: holds for (u, v) iff u = 0 with v in {1, 2, 3}, or u = 1 with v in {0, 4}, or u = 2 with v in {0, 5}, or u = 3 with v in {0, 6}, or (u, v) is (4, 1), (5, 2), or (6, 3).
-/

/-- Adjacency relation for the once-subdivided claw on Fin 7 with center 0 and branches 0-1-4, 0-2-5, 0-3-6. -/
def subdivided_claw_rel : Fin 7 → Fin 7 → Prop := fun u v =>
  (u = 0 ∧ (v = 1 ∨ v = 2 ∨ v = 3)) ∨
  (u = 1 ∧ (v = 0 ∨ v = 4)) ∨
  (u = 2 ∧ (v = 0 ∨ v = 5)) ∨
  (u = 3 ∧ (v = 0 ∨ v = 6)) ∨
  (u = 4 ∧ v = 1) ∨
  (u = 5 ∧ v = 2) ∨
  (u = 6 ∧ v = 3)

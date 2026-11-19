import AFTD.Prelude

/-!
# triangle_covered_marks_form_directed_cycle

Topic: combinatorics   Node: 2ca4a9c80d22

Provenance: helper lemma. Triangle exposure obstruction for the OP-874 truncation-coloring route.

If each triangle vertex marks one port and every triangle edge is marked by an endpoint, the marks orient the triangle as one of its two directed cycles.
-/

theorem triangle_covered_marks_form_directed_cycle :
    ∀ a b c : Fin 3,
      (a = 1 ∨ b = 0) → (b = 2 ∨ c = 1) → (a = 2 ∨ c = 0) →
      (a = 1 ∧ b = 2 ∧ c = 0) ∨ (a = 2 ∧ b = 0 ∧ c = 1) := by
  decide

import AFTD.Prelude

/-!
# triangle_covered_by_one_mark_per_vertex

Topic: combinatorics   Node: 44812ae3d18a

Provenance: helper lemma. Triangle exposure obstruction for the OP-874 truncation-coloring route.

If each vertex of a triangle marks at most one incident triangle edge and every triangle edge is marked by at least one endpoint, then every vertex marks a triangle edge rather than its outside port.
-/

theorem triangle_covered_by_one_mark_per_vertex :
    ∀ a b c : Fin 3,
      (a = 1 ∨ b = 0) → (b = 2 ∨ c = 1) → (a = 2 ∨ c = 0) →
      a ≠ 0 ∧ b ≠ 1 ∧ c ≠ 2 := by
  decide

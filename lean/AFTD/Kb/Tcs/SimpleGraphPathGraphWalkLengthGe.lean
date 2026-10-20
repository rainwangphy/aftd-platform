import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# simple_graph_path_graph_walk_length_ge

Topic: graphs   Node: ac279d2f2208

Provenance: helper lemma. for simple_graph_path_radio_labeling_four_mul_add_three (RT-4, OP-384)

Every walk in the path graph P_n from u to v has length at least |u - v|.
-/

theorem simple_graph_path_graph_walk_length_ge {n : ℕ} {u v : Fin n}
    (p : (SimpleGraph.pathGraph n).Walk u v) : |((u : ℕ) : ℤ) - ((v : ℕ) : ℤ)| ≤ p.length := by
  induction p with
  | nil => simp
  | cons h p ih =>
    rename_i a b c
    rw [SimpleGraph.pathGraph_adj] at h
    simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
    have h' : ((a : ℕ) : ℤ) + 1 = ((b : ℕ) : ℤ) ∨ ((b : ℕ) : ℤ) + 1 = ((a : ℕ) : ℤ) := by omega
    rcases abs_cases (((a : ℕ) : ℤ) - ((c : ℕ) : ℤ)) with ⟨h1, _⟩ | ⟨h1, _⟩ <;>
    rcases abs_cases (((b : ℕ) : ℤ) - ((c : ℕ) : ℤ)) with ⟨h2, _⟩ | ⟨h2, _⟩ <;>
    · rw [h1]; rw [h2] at ih; omega

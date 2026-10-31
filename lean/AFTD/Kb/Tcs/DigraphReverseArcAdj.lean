import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphReverseArc

/-!
# digraph_reverse_arc_adj

Topic: graphs   Node: 47751522810d

Provenance: helper lemma. step towards tournament_not_near_regular_exists_improving_tournament

Reversing the arc between u and v: the pair (u,v) gets the adjacency that (v,u) had, and any other pair keeps its adjacency.
-/

/-- Adjacency of the single-arc reversal: reversed on the pair {u,v}, unchanged elsewhere. -/
theorem digraph_reverse_arc_adj {n : ℕ} (D : Digraph (Fin n)) (u v : Fin n) :
    (∀ x y : Fin n, ¬ (x = u ∧ y = v) → ¬ (x = v ∧ y = u) →
      ((digraph_reverse_arc D u v).Adj x y ↔ D.Adj x y)) ∧
    ((digraph_reverse_arc D u v).Adj u v ↔ D.Adj v u) ∧
    ((digraph_reverse_arc D u v).Adj v u ↔ D.Adj u v) := by
  refine ⟨fun x y h1 h2 => ?_, ?_, ?_⟩
  · simp [h1, h2]
  · simp
  · simp

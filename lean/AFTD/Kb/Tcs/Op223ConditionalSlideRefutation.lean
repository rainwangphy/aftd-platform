import AFTD.Prelude
import AFTD.Kb.Tcs.Op223ExampleGraph
import AFTD.Kb.Tcs.Op223ExampleSlide
import AFTD.Kb.Tcs.IsSustainableTree

/-!
# op223_conditional_slide_refutation

Topic: graphs   Node: 6f0400a78bad

Provenance: helper lemma. arXiv:2610.17078 Open Problem 6.1; exact experiment 22883

If the example graph is sustainable and its two possible slides at the edge 4-5 are nonsustainable, then the universal leaf-slide predecessor assertion is false.
-/

theorem op223_conditional_slide_refutation
    (hX : is_sustainable_tree op223_example_graph)
    (h0 : ¬ is_sustainable_tree (op223_example_slide 0))
    (h6 : ¬ is_sustainable_tree (op223_example_slide 6)) :
    ¬ (∀ (n : ℕ) (X : SimpleGraph (Fin n)), is_sustainable_tree X →
      ∀ (u v : Fin n) (p : X.Walk u v), u ≠ v → p.IsPath →
        (∀ x ∈ p.support, x ≠ u → x ≠ v → Nat.card (X.neighborSet x) = 2) →
        3 ≤ Nat.card (X.neighborSet u) → Nat.card (X.neighborSet v) = 1 →
        ∃ b : Fin n, X.Adj u b ∧ ¬ X.Adj v b ∧ b ∉ p.support ∧
          is_sustainable_tree (X.deleteEdges {s(u, b)} ⊔ SimpleGraph.fromEdgeSet {s(v, b)})) := by
  intro h
  have h45 : op223_example_graph.Adj 4 5 := by
    simp [op223_example_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  let p : op223_example_graph.Walk 4 5 := .cons h45 .nil
  have hp : p.IsPath := by
    apply SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil
    simp
  have hint : ∀ x ∈ p.support, x ≠ 4 → x ≠ 5 →
      Nat.card (op223_example_graph.neighborSet x) = 2 := by
    intro x hx hx4 hx5
    simp [p] at hx
    rcases hx with rfl | rfl <;> contradiction
  have ht : op223_example_graph.neighborSet 4 = (({0, 5, 6} : Finset (Fin 8)) : Set (Fin 8)) := by
      ext x; fin_cases x <;> simp [SimpleGraph.neighborSet, op223_example_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
  have hu : 3 ≤ Nat.card (op223_example_graph.neighborSet 4) := by
    rw [Nat.card_coe_set_eq, ht, Set.ncard_coe_finset]
    decide
  have hv : Nat.card (op223_example_graph.neighborSet 5) = 1 := by
    have ht : op223_example_graph.neighborSet 5 = (({4} : Finset (Fin 8)) : Set (Fin 8)) := by
      ext x; fin_cases x <;> simp [SimpleGraph.neighborSet, op223_example_graph, SimpleGraph.fromEdgeSet_adj, Sym2.eq]
    rw [Nat.card_coe_set_eq, ht, Set.ncard_coe_finset]
    decide
  obtain ⟨b, hb, hn, hnot, hs⟩ := h 8 op223_example_graph hX 4 5 p (by decide) hp hint hu hv
  have hb' : b = 0 ∨ b = 5 ∨ b = 6 := by
    have hm : b ∈ op223_example_graph.neighborSet 4 := hb
    rw [ht] at hm
    simpa using hm
  rcases hb' with rfl | rfl | rfl
  · exact h0 hs
  · exact hnot (by simp [p])
  · exact h6 hs

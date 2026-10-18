import AFTD.Prelude

/-!
# op_258_card_fiber_sum

Topic: combinatorics   Node: 83e32fc0c3fc

Provenance: helper lemma. step towards op_258_triangle_forcing_implies_decay_ramsey

For any colouring c of the edges of the complete graph on Fin n, the sum over the colours actually used of the number of edges of that colour equals C(n,2).
-/

/-- The colour classes of any colouring of the edges of K_n partition its `C(n,2)` edges, so their cardinalities sum to `C(n,2)`. -/
theorem op_258_card_fiber_sum (n : ℕ) (c : (SimpleGraph.completeGraph (Fin n)).edgeSet → ℕ+) :
    (∑ i ∈ Finset.univ.image c,
      (((Finset.univ : Finset (SimpleGraph.completeGraph (Fin n)).edgeSet).filter (fun e => c e = i)).card : ℝ))
      = (n.choose 2 : ℝ) := by
  have hsplit : ((Finset.univ : Finset (SimpleGraph.completeGraph (Fin n)).edgeSet).card : ℕ)
      = ∑ i ∈ Finset.univ.image c,
        (((Finset.univ : Finset (SimpleGraph.completeGraph (Fin n)).edgeSet).filter (fun e => c e = i)).card) :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_image_of_mem c (Finset.mem_univ x))
  have hcard : ((Finset.univ : Finset (SimpleGraph.completeGraph (Fin n)).edgeSet).card : ℕ) = n.choose 2 := by
    rw [Finset.card_univ, ← SimpleGraph.edgeFinset_card (G := SimpleGraph.completeGraph (Fin n))]
    exact SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin n) |>.trans (by simp)
  have key : (∑ i ∈ Finset.univ.image c,
      (((Finset.univ : Finset (SimpleGraph.completeGraph (Fin n)).edgeSet).filter (fun e => c e = i)).card : ℝ))
      = (((Finset.univ : Finset (SimpleGraph.completeGraph (Fin n)).edgeSet).card : ℕ) : ℝ) := by
    rw [hsplit]
    push_cast
    rfl
  rw [key, hcard]

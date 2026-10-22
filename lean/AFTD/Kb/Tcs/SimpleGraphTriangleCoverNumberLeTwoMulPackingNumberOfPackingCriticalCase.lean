import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumberDeleteEdgeLtOrEq
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumberLeTwoMulPackingNumberOfDecreasingEdge
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumberEqZeroOfPackingNumberEqZero
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumberLeTwoOfPackingNumberLeOne
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumber
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber

/-!
# simple_graph_triangle_cover_number_le_two_mul_packing_number_of_packing_critical_case

Topic: graphs   Node: 42625581a2e6

Provenance: helper lemma. step towards simple_graph_triangle_cover_number_le_two_mul_packing_number

Tuza's conjecture follows from its packing-critical case: if every finite graph G with 2 ≤ ν(G) in which every edge deletion preserves ν satisfies τ(G) ≤ 2ν(G), then every finite graph satisfies τ(G) ≤ 2ν(G).
-/

/-- Reduction of Tuza's conjecture to its packing-critical case with ν ≥ 2 (the assembly half of the induction). -/
theorem simple_graph_triangle_cover_number_le_two_mul_packing_number_of_packing_critical_case
    (h : ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W),
      2 ≤ simple_graph_triangle_packing_number H →
      (∀ e ∈ H.edgeSet, simple_graph_triangle_packing_number (H.deleteEdges {e}) =
        simple_graph_triangle_packing_number H) →
      simple_graph_triangle_cover_number H ≤ 2 * simple_graph_triangle_packing_number H) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      simple_graph_triangle_cover_number G ≤ 2 * simple_graph_triangle_packing_number G := by
  intro n G
  have H_ind : ∀ (k : ℕ) (H : SimpleGraph (Fin n)),
      simple_graph_triangle_packing_number H ≤ k →
      simple_graph_triangle_cover_number H ≤ 2 * simple_graph_triangle_packing_number H := by
    intro k
    induction' k using Nat.strong_induction_on with k ih
    intro H hH
    rcases simple_graph_triangle_packing_number_delete_edge_lt_or_eq H with (⟨e, he, hlt⟩ | heq)
    · apply simple_graph_triangle_cover_number_le_two_mul_packing_number_of_decreasing_edge H _ e he hlt
      intro H' hH'
      apply ih (simple_graph_triangle_packing_number H') (by omega) H' (le_refl _)
    · rcases le_or_gt 2 (simple_graph_triangle_packing_number H) with h2 | hlt2
      · exact h (Fin n) H h2 heq
      · have hle1 : simple_graph_triangle_packing_number H ≤ 1 := by omega
        rcases (simple_graph_triangle_packing_number H).eq_zero_or_pos with h0 | hpos
        · rw [simple_graph_triangle_cover_number_eq_zero_of_packing_number_eq_zero H h0, h0]
        · have hcov := simple_graph_triangle_cover_number_le_two_of_packing_number_le_one H hle1
          omega
  exact H_ind (simple_graph_triangle_packing_number G) G (le_refl _)

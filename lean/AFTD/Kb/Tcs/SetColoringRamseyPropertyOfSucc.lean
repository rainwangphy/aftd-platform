import AFTD.Prelude
import AFTD.Kb.Tcs.SetColoringRamseyProperty
import AFTD.Kb.Tcs.SupportGraph

/-!
# set_coloring_ramsey_property_of_succ

Topic: combinatorics   Node: 0f2d00449f37

Provenance: formalization of a published result. Source: arXiv:2611.15376 Section 7, Eq (37)

For any simple graph G on a type V and natural numbers r, s, t, N, if set_coloring_ramsey_property G r s (t + 1) N holds, then set_coloring_ramsey_property G r s t N holds.
-/

open scoped Classical in
/-- Monotonicity of set-coloring Ramsey property in the intersection parameter t: if every coloring has a (t+1)-monochromatic copy, it has a t-monochromatic copy. -/
theorem set_coloring_ramsey_property_of_succ
    {V : Type*} (G : SimpleGraph V) (r s t N : ℕ)
    (h : set_coloring_ramsey_property G r s (t + 1) N) :
    set_coloring_ramsey_property G r s t N := by
  intro ϕ hϕ
  obtain ⟨T_succ, hT_card, hT_cont⟩ := h ϕ hϕ
  have hpos : 0 < T_succ.card := by omega
  have hne : T_succ.Nonempty := Finset.card_pos.mp hpos
  obtain ⟨x, hx⟩ := hne
  refine ⟨T_succ.erase x, ?_, ?_⟩
  · rw [Finset.card_erase_of_mem hx, hT_card]
    exact Nat.succ_sub_one t
  · obtain ⟨f⟩ := hT_cont
    refine ⟨⟨⟨f.toHom, fun hadj => ?_⟩, f.injective'⟩⟩
    have hle : support_graph ϕ T_succ ≤ support_graph ϕ (T_succ.erase x) := by
      intro v w hw
      rw [support_graph] at hw ⊢
      rw [SimpleGraph.fromEdgeSet_adj] at hw ⊢
      refine ⟨?_, hw.2⟩
      rcases hw.1 with ⟨hedge, hsub⟩
      exact ⟨hedge, (Finset.erase_subset x T_succ).trans hsub⟩
    exact hle (f.toHom.map_rel hadj)

import AFTD.Prelude

/-!
# finite_single_outside_sets_biunion_card_le

Topic: combinatorics   Node: b7d3fa58b075

Provenance: helper lemma. Counting forbidden vertices in simple_graph_triangle_packing_pair_deletion_forcing_quadratic_kernel; state/campaigns/triangle_reductions/quadratic_kernel_in687.md.

For a finite family of sets each containing at most one point outside S, their union contains at most one such point per set.
-/

theorem finite_single_outside_sets_biunion_card_le {V : Type*} [DecidableEq V]
    (S : Finset V) (R : Finset (Finset V))
    (houtside : ∀ t ∈ R, (t \ S).card ≤ 1) :
    ((R.biUnion id) \ S).card ≤ R.card := by
  classical
  have hs : (R.biUnion id) \ S ⊆ R.biUnion (fun t => t \ S) := by
    intro v hv
    obtain ⟨hvr,hvs⟩ := Finset.mem_sdiff.mp hv
    obtain ⟨t,ht,hvt⟩ := Finset.mem_biUnion.mp hvr
    exact Finset.mem_biUnion.mpr ⟨t,ht,Finset.mem_sdiff.mpr ⟨hvt,hvs⟩⟩
  have hc := Finset.card_le_card hs
  have hB := Finset.card_biUnion_le_card_mul R (fun t => t \ S) 1 houtside
  simp only [Nat.mul_one] at hB
  omega

import AFTD.Prelude

/-!
# finite_sym2_cross_outside_endpoints_card_le

Topic: combinatorics   Node: e71a8039e61e

Provenance: helper lemma. Counting forbidden vertices in simple_graph_triangle_packing_pair_deletion_forcing_quadratic_kernel; state/campaigns/triangle_reductions/quadratic_kernel_in687.md.

For a finite set of unordered pairs, the union of outside endpoints of pairs incident with S has cardinality at most the number of pairs.
-/

theorem finite_sym2_cross_outside_endpoints_card_le {V : Type*} [DecidableEq V]
    (S : Finset V) (D : Finset (Sym2 V)) :
    ((D.filter (fun e => ∃ a ∈ S, a ∈ e.toFinset)).biUnion
      (fun e => e.toFinset \ S)).card ≤ D.card := by
  classical
  let D' := D.filter (fun e => ∃ a ∈ S, a ∈ e.toFinset)
  change (D'.biUnion fun e => e.toFinset \ S).card ≤ D.card
  have hone : ∀ e ∈ D', (e.toFinset \ S).card ≤ 1 := by
    intro e he
    obtain ⟨a,haS,hae⟩ := (Finset.mem_filter.mp he).2
    have hs : e.toFinset \ S ⊆ e.toFinset.erase a := by
      intro v hv
      obtain ⟨hve,hvS⟩ := Finset.mem_sdiff.mp hv
      exact Finset.mem_erase.mpr ⟨by intro h; subst v; exact hvS haS,hve⟩
    have hc := Finset.card_le_card hs
    rw [Finset.card_erase_of_mem hae] at hc
    have hec : e.toFinset.card ≤ 2 := by
      rw [Sym2.card_toFinset]
      split_ifs <;> omega
    have hp : 0 < e.toFinset.card := Finset.card_pos.mpr ⟨a,hae⟩
    omega
  have hB : (D'.biUnion fun e => e.toFinset \ S).card ≤ D'.card * 1 :=
    Finset.card_biUnion_le_card_mul D' (fun e => e.toFinset \ S) 1 hone
  have hD : D'.card ≤ D.card := Finset.card_le_card (Finset.filter_subset _ _)
  simp only [Nat.mul_one] at hB
  omega

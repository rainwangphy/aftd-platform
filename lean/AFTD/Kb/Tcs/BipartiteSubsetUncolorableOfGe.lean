import AFTD.Prelude
import AFTD.Kb.Tcs.BipartiteSubsetStandardListColorable
import AFTD.Kb.Tcs.BipartiteSubsetGraph

/-!
# bipartite_subset_uncolorable_of_ge

Topic: graphs   Node: bd2fe01b1e13

Provenance: helper lemma. arXiv:2610.42094, Section 1.3

For integers k ≥ 1 and r with k ≤ r, the bipartite subset graph bipartite_subset_graph k r has no proper coloring from its standard lists, that is, ¬ bipartite_subset_standard_list_colorable k r.
-/

/-- For r ≥ k, G(k,r) is complete bipartite and has no proper list coloring from standard lists. -/
theorem bipartite_subset_uncolorable_of_ge (k r : ℕ) (hk : 1 ≤ k) (hr : k ≤ r) :
    ¬ bipartite_subset_standard_list_colorable k r := by
  have _ := hk
  intro ⟨c, hc⟩
  let C_A : Finset (Fin (2 * k - 1)) :=
    Finset.image (fun S : {S : Finset (Fin (2 * k - 1)) // S.card = k} => c (Sum.inl S)) Finset.univ
  have h_ge : k ≤ C_A.card := by
    by_contra! h_lt
    have h_le : k ≤ (Finset.univ \ C_A).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ C_A), Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨S, hS_sub, hS_card⟩ := Finset.exists_subset_card_eq h_le
    let S_val : {S : Finset (Fin (2 * k - 1)) // S.card = k} := ⟨S, hS_card⟩
    have hcS : c (Sum.inl S_val) ∈ S := hc (Sum.inl S_val)
    have h_not_mem : c (Sum.inl S_val) ∉ C_A := by
      have := hS_sub hcS
      exact (Finset.mem_sdiff.mp this).2
    have h_mem : c (Sum.inl S_val) ∈ C_A := by
      apply Finset.mem_image_of_mem
      exact Finset.mem_univ S_val
    exact h_not_mem h_mem
  obtain ⟨T, hT_sub, hT_card⟩ := Finset.exists_subset_card_eq h_ge
  let T_val : {T : Finset (Fin (2 * k - 1)) // T.card = k} := ⟨T, hT_card⟩
  have hcT : c (Sum.inr T_val) ∈ T := hc (Sum.inr T_val)
  have h_mem : c (Sum.inr T_val) ∈ C_A := hT_sub hcT
  rcases Finset.mem_image.mp h_mem with ⟨S_val, -, hS_eq⟩
  have hadj : (bipartite_subset_graph k r).Adj (Sum.inl S_val) (Sum.inr T_val) := by
    change (S_val.1 ∩ T_val.1).card ≤ r
    exact le_trans (Finset.card_le_card Finset.inter_subset_left) (S_val.2.le.trans hr)
  exact c.valid hadj hS_eq

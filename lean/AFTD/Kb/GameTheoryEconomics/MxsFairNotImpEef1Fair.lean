import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEef1Fair
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.IsMxsFair

/-!
# mxs_fair_not_imp_eef1_fair

Topic: fair_division   Node: fd9f1a3136b6

Garg-Sharma open problem 1 has a negative answer: for additive goods and equal entitlements, MXS does not imply EEF1, already for three agents. Example: twelve goods worth 2,2,2,1,2,2,2,3,2,2,2,3 to every agent; agent 0 holds the goods worth 1, 3, 3, which is MXS-fair via the EFX certificate {2,2,2,1}, {2,2,2,3}, {2,2,2,3}, but not EEF1-fair because one of the other two agents always gets five of the nine goods worth 2.
-/

/-- Garg-Sharma open problem 1 (arXiv:2502.02815 v3, Sec. 6) has a negative answer: for additive goods and equal entitlements, MXS does not imply EEF1, already for three agents. -/
theorem mxs_fair_not_imp_eef1_fair :
    ¬ ∀ (n m : ℕ) (u : Fin n → Fin m → ℝ), (∀ i j, 0 ≤ u i j) →
      ∀ (σ : Fin m → Fin n) (i : Fin n),
        is_mxs_fair (fun k => additive_valuation (u k)) σ i →
        is_eef1_fair (fun k => additive_valuation (u k)) σ i := by
  intro h
  -- twelve goods; agent 0 holds {3, 7, 11}, worth 1 + 3 + 3 = 7; the other nine goods are worth 2
  let w : Fin 12 → ℕ := ![2, 2, 2, 1, 2, 2, 2, 3, 2, 2, 2, 3]
  let vN : Finset (Fin 12) → ℕ := fun S => ∑ j ∈ S, w j
  let u : Fin 3 → Fin 12 → ℝ := fun _ j => (w j : ℝ)
  have hv : ∀ k S, additive_valuation (u k) S = (vN S : ℝ) := by
    intro k S
    simp [additive_valuation, u, vN]
  have hmono : ∀ S S' : Finset (Fin 12), S ⊆ S' → vN S ≤ vN S' := fun S S' hSS' =>
    Finset.sum_le_sum_of_subset hSS'
  let σ : Fin 12 → Fin 3 := ![1, 1, 1, 0, 1, 1, 1, 0, 2, 2, 2, 0]
  -- the EFX certificate: X = {0,1,2,3} worth 7, and two bundles {2,2,2,3} worth 7 after removing any good
  let τ : Fin 12 → Fin 3 := ![0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2]
  have hX : vN (bundle_of τ 0) = 7 := by decide +kernel
  have hA7 : vN (bundle_of σ 0) = 7 := by decide +kernel
  have hB : ∀ j : Fin 3, j ≠ 0 → ∀ g ∈ bundle_of τ j, vN ((bundle_of τ j).erase g) ≤ 7 := by
    decide +kernel
  have hmxs : is_mxs_fair (fun k => additive_valuation (u k)) σ 0 := by
    refine ⟨τ, fun j hj => Or.inr ⟨fun S hS hlt => ?_, fun S hS hlt => ?_⟩, ?_⟩
    · simp only [hv] at hlt ⊢
      have hlt' : vN (bundle_of τ 0) < vN (bundle_of τ 0 ∪ S) := by exact_mod_cast hlt
      obtain ⟨g, hg⟩ : S.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        rintro rfl
        simp at hlt'
      have h1 : bundle_of τ j \ S ⊆ (bundle_of τ j).erase g := by
        intro x hx
        rw [Finset.mem_sdiff] at hx
        exact Finset.mem_erase.2 ⟨fun hxg => hx.2 (hxg ▸ hg), hx.1⟩
      have := (hmono _ _ h1).trans (hB j hj g (hS hg))
      rw [hX]
      exact_mod_cast this
    · simp only [hv] at hlt
      have hlt' : vN (bundle_of τ 0) < vN (bundle_of τ 0 \ S) := by exact_mod_cast hlt
      exact absurd (hmono _ _ Finset.sdiff_subset) (not_le.2 hlt')
    · simp only [hv]
      rw [hX, hA7]
  obtain ⟨τ', hb, hef1⟩ := h 3 12 u (fun _ j => by simp [u]) σ 0 hmxs
  have hcases : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide
  have hx0 : ∀ x, x ∈ bundle_of τ' 0 ↔ τ' x = 0 := by
    intro x
    simp [bundle_of]
  have hσ0 : ∀ x, x ∈ bundle_of σ 0 ↔ σ x = 0 := by
    intro x
    simp [bundle_of]
  have hw2 : ∀ x : Fin 12, σ x ≠ 0 → w x = 2 := by decide +kernel
  -- every good another agent gets under τ' lies outside agent 0's bundle, so it is worth 2
  have hval2 : ∀ j : Fin 3, j ≠ 0 → ∀ S ⊆ bundle_of τ' j, vN S = 2 * S.card := by
    intro j hj S hS
    show ∑ x ∈ S, w x = 2 * S.card
    rw [Finset.card_eq_sum_ones, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    have hx' := hS hx
    simp only [bundle_of, Finset.mem_filter, Finset.mem_univ, true_and] at hx'
    have hσx : σ x ≠ 0 := by
      intro h0
      have hmem : x ∈ bundle_of τ' 0 := by
        rw [hb]
        exact (hσ0 x).2 h0
      rw [hx0, hx'] at hmem
      exact hj hmem
    rw [hw2 x hσx]
    rfl
  -- agents 1 and 2 share the nine goods outside agent 0's bundle
  have hcard : (bundle_of τ' 1).card + (bundle_of τ' 2).card = 9 := by
    have hdisj : Disjoint (bundle_of τ' 1) (bundle_of τ' 2) := by
      rw [Finset.disjoint_left]
      intro x h1 h2
      simp only [bundle_of, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      rw [h1] at h2
      exact absurd h2 (by decide)
    rw [← Finset.card_union_of_disjoint hdisj]
    have hU : bundle_of τ' 1 ∪ bundle_of τ' 2 = (bundle_of σ 0)ᶜ := by
      ext x
      rw [Finset.mem_union, Finset.mem_compl, ← hb, hx0]
      simp only [bundle_of, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hcases (τ' x) with hk | hk | hk <;> simp [hk]
    have h3 : (bundle_of σ 0).card = 3 := by decide +kernel
    rw [hU, Finset.card_compl, h3]
    simp
  -- an agent with five or more of them is envied by agent 0 even after removing any good
  have hfail : ∀ j : Fin 3, j ≠ 0 → 5 ≤ (bundle_of τ' j).card → False := by
    intro j hj h5
    have hB2 := hval2 j hj (bundle_of τ' j) (le_refl _)
    rcases hef1 j hj with h1 | ⟨g, hg, h2⟩ | ⟨c, _, h3⟩
    · simp only [hv, hb] at h1
      have h1' : vN (bundle_of τ' j) ≤ vN (bundle_of σ 0) := by exact_mod_cast h1
      omega
    · simp only [hv, hb] at h2
      have h2' : vN ((bundle_of τ' j).erase g) ≤ vN (bundle_of σ 0) := by exact_mod_cast h2
      have he := hval2 j hj _ (Finset.erase_subset g _)
      rw [Finset.card_erase_of_mem hg] at he
      omega
    · simp only [hv, hb] at h3
      have h3' : vN (bundle_of τ' j) ≤ vN ((bundle_of σ 0).erase c) := by exact_mod_cast h3
      have hm := hmono _ _ (Finset.erase_subset c (bundle_of σ 0))
      omega
  by_cases h5 : 5 ≤ (bundle_of τ' 1).card
  · exact hfail 1 (by decide) h5
  · exact hfail 2 (by decide) (by omega)

import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEjrCommittee
import AFTD.Kb.GameTheoryEconomics.IsEjrCohesiveGroup

/-!
# is_ejr_committee_iff_undersatisfied_supporters

Topic: social_choice   Node: c677a4e91dc8

Provenance: helper lemma. Helper for ejr_committee_monotone_chain_exists (OP-22; arXiv:2007.01795, open problems Q2): finite witness criterion used in exact profile synthesis and committee-subset dynamic programming.

A committee W of size k satisfies EJR exactly when, for each positive ell and each ell-element candidate set T, fewer than ell*n/k voters both approve every member of T and approve fewer than ell members of W, stated without division as underrepresented-supporter count times k < ell*n.
-/

theorem is_ejr_committee_iff_undersatisfied_supporters {n m : ℕ}
    (A : Fin n → Finset (Fin m)) (k : ℕ) (W : Finset (Fin m)) :
    is_ejr_committee A k W ↔ W.card = k ∧
      ∀ ℓ, 1 ≤ ℓ → ∀ T : Finset (Fin m), T.card = ℓ →
        (Finset.univ.filter fun i => T ⊆ A i ∧ (A i ∩ W).card < ℓ).card * k < ℓ * n := by
  classical
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro ℓ hℓ T hT
    by_contra hbad
    let G := Finset.univ.filter fun i => T ⊆ A i ∧ (A i ∩ W).card < ℓ
    have hsize : ℓ * n ≤ G.card * k := Nat.le_of_not_gt hbad
    have hsub : T ⊆ Finset.univ.filter fun c => ∀ i ∈ G, c ∈ A i := by
      intro c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro i hi
      exact (Finset.mem_filter.mp hi).2.1 hc
    have hcoh : is_ejr_cohesive_group A k ℓ G :=
      ⟨hsize, by rw [← hT]; exact Finset.card_le_card hsub⟩
    obtain ⟨i, hi, hsat⟩ := h.2 ℓ hℓ G hcoh
    have hlt := (Finset.mem_filter.mp hi).2.2
    omega
  · rintro ⟨hcard, h⟩
    refine ⟨hcard, ?_⟩
    intro ℓ hℓ G hcoh
    by_contra hnone
    push Not at hnone
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcoh.2
    let H := Finset.univ.filter fun i => T ⊆ A i ∧ (A i ∩ W).card < ℓ
    have hGH : G ⊆ H := by
      intro i hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · intro c hc
        exact (Finset.mem_filter.mp (hTsub hc)).2 i hi
      · exact hnone i hi
    have hle := Nat.mul_le_mul_right k (Finset.card_le_card hGH)
    have hlt := h ℓ hℓ T hTcard
    have hsize := hcoh.1
    change H.card * k < ℓ * n at hlt
    omega

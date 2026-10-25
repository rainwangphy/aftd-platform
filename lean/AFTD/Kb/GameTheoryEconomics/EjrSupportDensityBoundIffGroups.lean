import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EjrSupportDensityBound

/-!
# ejr_support_density_bound_iff_groups

Topic: social_choice   Node: f91222e98512

Provenance: helper lemma. Supporting work for OP-22, arXiv:2007.01795, Q2, and the proposed max-group-density invariant in memory attempt 4342. These helpers neither settle full-chain existence nor refute the actual greedy rule. No research advance is claimed.

The finite supporter bound is equivalent to the corresponding bound on every commonly approving group whose members all have utility below a positive demand.
-/

theorem ejr_support_density_bound_iff_groups {n m : ℕ}
    (A : Fin n → Finset (Fin m)) (q : ℕ) (W : Finset (Fin m)) :
    ejr_support_density_bound A q W ↔
      ∀ ℓ, 1 ≤ ℓ → ∀ G : Finset (Fin n),
        ℓ ≤ (Finset.univ.filter fun c => ∀ i ∈ G, c ∈ A i).card →
        (∀ i ∈ G, (A i ∩ W).card < ℓ) → G.card * q ≤ ℓ * n := by
  classical
  constructor
  · intro h ℓ hℓ G hcommon hunsat
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcommon
    let H := Finset.univ.filter fun i => T ⊆ A i ∧ (A i ∩ W).card < ℓ
    have hGH : G ⊆ H := by
      intro i hi
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, hunsat i hi⟩
      intro c hc
      exact (Finset.mem_filter.mp (hTsub hc)).2 i hi
    have hle := Nat.mul_le_mul_right q (Finset.card_le_card hGH)
    have hb := h T
    rw [hTcard] at hb
    exact hle.trans hb
  · intro h T
    by_cases hT : T.Nonempty
    · let G := Finset.univ.filter fun i => T ⊆ A i ∧ (A i ∩ W).card < T.card
      have hsub : T ⊆ Finset.univ.filter fun c => ∀ i ∈ G, c ∈ A i := by
        intro c hc
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        intro i hi
        exact (Finset.mem_filter.mp hi).2.1 hc
      exact h T.card (by have := Finset.card_pos.mpr hT; omega) G
        (Finset.card_le_card hsub) (fun i hi => (Finset.mem_filter.mp hi).2.2)
    · have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
      simp [he]

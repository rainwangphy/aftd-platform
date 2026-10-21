import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsPickingSequencePne
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcome
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequence
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuationToValuation
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# round_robin_pne_envy_zero_ef1_of_deviation_certificate

Topic: fair_division   Node: b5566707ce64

Provenance: helper lemma. step for round_robin_pne_envy_zero_ef1_of_two_mul_add_one (research thread RT-3)

If the deviation certificate of round_robin_two_mul_add_one_deviation_certificate holds for agent i ≠ 0, then at a pure Nash equilibrium of Round-Robin (2n+1 goods, nonnegative additive valuations) agent i is EF1 towards agent 0.
-/

theorem round_robin_pne_envy_zero_ef1_of_deviation_certificate (n : ℕ) [NeZero n]
    (w : Fin n → Fin (2 * n + 1) → ℝ) (hw : ∀ i g, 0 ≤ w i g)
    (rank : Fin n → Fin (2 * n + 1) ≃ Fin (2 * n + 1))
    (h : is_picking_sequence_pne
      (SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation ⟨w⟩)
      (round_robin_sequence n (2 * n + 1)) rank)
    (i : Fin n) (hi : i ≠ 0)
    (hcert : ∃ g ∈ picking_sequence_outcome (round_robin_sequence n (2 * n + 1)) rank 0,
      (∃ r : Fin (2 * n + 1) ≃ Fin (2 * n + 1),
        picking_sequence_outcome (round_robin_sequence n (2 * n + 1)) rank 0 \ {g} ⊆
          picking_sequence_outcome (round_robin_sequence n (2 * n + 1))
            (Function.update rank i r) i) ∨
      (∃ r₁ r₂ : Fin (2 * n + 1) ≃ Fin (2 * n + 1), ∀ x : Fin (2 * n + 1),
        (if x ∈ picking_sequence_outcome (round_robin_sequence n (2 * n + 1)) rank i then 1 else 0) +
          (if x ∈ picking_sequence_outcome (round_robin_sequence n (2 * n + 1)) rank 0 \ {g}
            then 1 else 0) ≤
        (if x ∈ picking_sequence_outcome (round_robin_sequence n (2 * n + 1))
            (Function.update rank i r₁) i then 1 else 0) +
          (if x ∈ picking_sequence_outcome (round_robin_sequence n (2 * n + 1))
            (Function.update rank i r₂) i then 1 else 0 : ℕ))) :
    ∃ g ∈ picking_sequence_outcome (round_robin_sequence n (2 * n + 1)) rank 0,
      (SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation ⟨w⟩).val i
          (picking_sequence_outcome (round_robin_sequence n (2 * n + 1)) rank 0 \ {g}) ≤
        (SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation ⟨w⟩).val i
          (picking_sequence_outcome (round_robin_sequence n (2 * n + 1)) rank i) := by
  have _ := hi
  obtain ⟨g, hg, hcases⟩ := hcert
  refine ⟨g, hg, ?_⟩
  simp only [SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation]
  rcases hcases with ⟨r, hr⟩ | ⟨r₁, r₂, hr₁₂⟩
  · have hpne := h i r
    simp only [SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation] at hpne
    have hsub : ∑ x ∈ picking_sequence_outcome (round_robin_sequence n (2 * n + 1)) rank 0 \ {g}, w i x ≤
        ∑ x ∈ picking_sequence_outcome (round_robin_sequence n (2 * n + 1)) (Function.update rank i r) i, w i x :=
      Finset.sum_le_sum_of_subset_of_nonneg hr (fun x _ _ => hw i x)
    linarith
  · have hpne₁ := h i r₁
    have hpne₂ := h i r₂
    simp only [SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation] at hpne₁ hpne₂
    have hsum : ∑ x : Fin (2 * n + 1),
        ((if x ∈ picking_sequence_outcome (round_robin_sequence n (2 * n + 1)) rank i then w i x else 0) +
         (if x ∈ picking_sequence_outcome (round_robin_sequence n (2 * n + 1)) rank 0 \ {g} then w i x else 0)) ≤
        ∑ x : Fin (2 * n + 1),
        ((if x ∈ picking_sequence_outcome (round_robin_sequence n (2 * n + 1)) (Function.update rank i r₁) i then w i x else 0) +
         (if x ∈ picking_sequence_outcome (round_robin_sequence n (2 * n + 1)) (Function.update rank i r₂) i then w i x else 0)) := by
      apply Finset.sum_le_sum
      intro x _
      have hc := hr₁₂ x
      have hwx := hw i x
      split_ifs at * <;> linarith
    simp only [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter] at hsum
    linarith

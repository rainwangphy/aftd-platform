import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsAdmissibleLottery
import AFTD.Kb.GameTheoryEconomics.IsEnvyFreeCoupling
import AFTD.Kb.GameTheoryEconomics.SampfordCouplingLoss
import AFTD.Kb.GameTheoryEconomics.IsEnvyFreeOutcome

/-!
# envy_free_coupling_loss_mem_unit_interval

Topic: social_choice   Node: 60e4a49fb7a9

Provenance: helper lemma. folklore

For n parties, vote shares p, house size H, and any coupling prob of admissible lotteries distH at H and distH1 at H + 1, the coupling loss sampfordCouplingLoss p H prob lies in [0, 1].
-/

/-- The house-monotonicity coupling loss of any valid coupling of admissible lotteries lies between 0 and 1. -/
theorem envy_free_coupling_loss_mem_unit_interval {n : ℕ} (p : Fin n → ℝ) (H : ℕ)
    (distH distH1 : Finset (Fin n) → ℝ) (prob : Finset (Fin n) → Finset (Fin n) → ℝ)
    (hprob : is_envy_free_coupling p H distH distH1 prob)
    (hdistH : is_admissible_lottery p H distH)
    (hdistH1 : is_admissible_lottery p (H + 1) distH1) :
    0 ≤ sampfordCouplingLoss p H prob ∧ sampfordCouplingLoss p H prob ≤ 1 := by
  have hmarg : ∀ S ∈ Finset.powersetCard (H - ∑ i, ⌊(H:ℝ) * p i⌋₊) Finset.univ,
      ∑ T ∈ Finset.powersetCard (H + 1 - ∑ i, ⌊((H:ℝ) + 1) * p i⌋₊) Finset.univ,
        prob S T = distH S := hprob.2.1
  have hsum : ∑ S ∈ Finset.powersetCard (H - ∑ i, ⌊(H:ℝ) * p i⌋₊) Finset.univ, distH S = 1 :=
    hdistH.2.2.1
  constructor
  · simp only [sampfordCouplingLoss]
    apply Finset.sum_nonneg
    intro S _
    apply Finset.sum_nonneg
    intro T _
    split_ifs with h
    · exact hprob.1 S T
    · exact le_refl 0
  · simp only [sampfordCouplingLoss]
    calc ∑ S ∈ Finset.powersetCard (H - ∑ i, ⌊(H:ℝ) * p i⌋₊) Finset.univ,
          ∑ T ∈ Finset.powersetCard (H + 1 - ∑ i, ⌊((H:ℝ) + 1) * p i⌋₊) Finset.univ,
            (if ∃ i, (⌊((H:ℝ) + 1) * p i⌋₊ + if i ∈ T then 1 else 0) < ⌊(H:ℝ) * p i⌋₊ + (if i ∈ S then 1 else 0)
             then prob S T else 0)
        ≤ ∑ S ∈ Finset.powersetCard (H - ∑ i, ⌊(H:ℝ) * p i⌋₊) Finset.univ,
          ∑ T ∈ Finset.powersetCard (H + 1 - ∑ i, ⌊((H:ℝ) + 1) * p i⌋₊) Finset.univ, prob S T := by
          apply Finset.sum_le_sum
          intro S _
          apply Finset.sum_le_sum
          intro T _
          split_ifs with h
          · exact le_refl _
          · exact hprob.1 S T
      _ = ∑ S ∈ Finset.powersetCard (H - ∑ i, ⌊(H:ℝ) * p i⌋₊) Finset.univ, distH S := by
          apply Finset.sum_congr rfl
          intro S hS
          exact hmarg S hS
      _ = 1 := hsum

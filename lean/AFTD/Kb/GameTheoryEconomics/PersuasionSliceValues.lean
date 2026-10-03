import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceCoord
import AFTD.Kb.GameTheoryEconomics.PersuasionMarginal
import AFTD.Kb.GameTheoryEconomics.PersuasionSlicePrior
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceState
import AFTD.Kb.GameTheoryEconomics.PersuasionMaxReceiverUtility
import AFTD.Kb.GameTheoryEconomics.PersuasionPriorUtility
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceCardCoord
import AFTD.Kb.GameTheoryEconomics.PersuasionSlicePriorIsBitPrior
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceSchemeObedient
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceSchemeSenderUtility
import AFTD.Kb.GameTheoryEconomics.PersuasionPairOrReceiverAddSender
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceCoupling
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceCouplingMarginal
import AFTD.Kb.GameTheoryEconomics.PersuasionReceiverUtility
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceScheme
import AFTD.Kb.GameTheoryEconomics.IsSenderOptimalScheme
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceSenderLe
import AFTD.Kb.GameTheoryEconomics.PersuasionReceiverAddSenderLe

/-!
# persuasion_slice_values

Topic: mechanism_design   Node: c2c25bccfc61

R_max and R_0 for the slice prior.
-/

open Finset in
/-- Every coordinate of the slice prior has marginal `m/(2m+1)`. -/
lemma persuasion_slice_marginal (m : ℕ) (i : persuasion_slice_coord m) :
    persuasion_marginal (persuasion_slice_prior m) i = m / (2 * m + 1 : ℝ) := by
  classical
  unfold persuasion_marginal persuasion_slice_prior
  have e : ∀ x : persuasion_slice_coord m → Bool, (if x i = true then
      ∑ s, (if persuasion_slice_state m s = x then 1 / (2 * m + 1 : ℝ) else 0) else 0) =
      ∑ s, if persuasion_slice_state m s = x then
        (if persuasion_slice_state m s i = true then 1 / (2 * m + 1 : ℝ) else 0) else 0 := by
    intro x
    by_cases hx : x i = true
    · rw [if_pos hx]
      apply sum_congr rfl; intro s _
      by_cases h : persuasion_slice_state m s = x
      · rw [if_pos h, if_pos h, h, if_pos hx]
      · rw [if_neg h, if_neg h]
    · rw [if_neg hx]
      symm
      apply sum_eq_zero; intro s _
      by_cases h : persuasion_slice_state m s = x
      · rw [if_pos h, h, if_neg hx]
      · rw [if_neg h]
  rw [sum_congr rfl (fun x _ => e x), sum_comm]
  simp only [sum_ite_eq, Finset.mem_univ, if_true]
  rw [← sum_filter, Finset.sum_const, nsmul_eq_mul]
  have : (Finset.univ.filter (fun s => persuasion_slice_state m s i = true)) = i.1 := by
    ext s; simp [persuasion_slice_state]
  rw [this, i.2]
  ring

open Finset in
/-- `R_max` and `R_0` for the slice prior. -/
theorem persuasion_slice_values (m : ℕ) (hm : 1 ≤ m) :
    persuasion_max_receiver_utility (persuasion_slice_prior m) =
        (2 * m - 1).choose m + (2 * m + 1).choose m * (m / (2 * m + 1 : ℝ)) ∧
      persuasion_prior_utility (persuasion_slice_prior m) =
        (2 * m + 1).choose m * ((m + 1) / (2 * m + 1 : ℝ)) := by
  classical
  have hK : (0 : ℝ) < 2 * m + 1 := by positivity
  have hP : ∑ i, persuasion_marginal (persuasion_slice_prior m) i =
      (2 * m + 1).choose m * (m / (2 * m + 1 : ℝ)) := by
    simp only [persuasion_slice_marginal, Finset.sum_const, card_univ, persuasion_slice_card_coord,
      nsmul_eq_mul]
  have hμ := (persuasion_slice_prior_is_bit_prior m).2
  have hobs := persuasion_slice_scheme_obedient m hm
  have hS := persuasion_slice_scheme_sender_utility m hm
  have hRS := persuasion_pair_or_receiver_add_sender (persuasion_slice_prior m) hμ
    (persuasion_slice_coupling m) (persuasion_slice_coupling_marginal m hm)
  rw [persuasion_slice_card_coord, hP] at hRS
  have hR : persuasion_receiver_utility (persuasion_slice_scheme m) =
      (2 * m - 1).choose m + (2 * m + 1).choose m * (m / (2 * m + 1 : ℝ)) := by
    unfold persuasion_slice_scheme at hS ⊢
    linarith
  have hopt : is_sender_optimal_scheme (persuasion_slice_prior m) (persuasion_slice_scheme m) :=
    ⟨hobs, fun q' hq' => hS ▸ persuasion_slice_sender_le m hm q' hq'⟩
  refine ⟨?_, ?_⟩
  · apply IsGreatest.csSup_eq
    refine ⟨⟨persuasion_slice_scheme m, hopt, hR.symm⟩, ?_⟩
    rintro r ⟨q, ⟨hq, hqopt⟩, rfl⟩
    have h1 := persuasion_receiver_add_sender_le _ hμ q hq
    rw [persuasion_slice_card_coord, hP] at h1
    have h2 := hqopt _ hobs
    rw [hS] at h2
    linarith
  · unfold persuasion_prior_utility
    simp only [persuasion_slice_marginal, Finset.sum_const, card_univ, persuasion_slice_card_coord,
      nsmul_eq_mul]
    congr 1
    rw [max_eq_right]
    · field_simp; ring
    · rw [div_le_iff₀ hK]
      have : (m : ℝ) / (2 * m + 1) * (2 * m + 1) = m := by field_simp
      nlinarith

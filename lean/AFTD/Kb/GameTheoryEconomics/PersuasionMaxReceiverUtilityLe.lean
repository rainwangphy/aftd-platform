import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsBitPrior
import AFTD.Kb.GameTheoryEconomics.PersuasionMarginal
import AFTD.Kb.GameTheoryEconomics.PersuasionSenderUtility
import AFTD.Kb.GameTheoryEconomics.PersuasionPairOrScheme
import AFTD.Kb.GameTheoryEconomics.PersuasionPairOrSenderUtility
import AFTD.Kb.GameTheoryEconomics.PersuasionMaxReceiverUtility
import AFTD.Kb.GameTheoryEconomics.PersuasionPriorUtility
import AFTD.Kb.GameTheoryEconomics.PersuasionPairOrSchemeObedient
import AFTD.Kb.GameTheoryEconomics.IsSenderOptimalScheme
import AFTD.Kb.GameTheoryEconomics.PersuasionReceiverUtility
import AFTD.Kb.GameTheoryEconomics.PersuasionReceiverAddSenderLe

/-!
# persuasion_max_receiver_utility_le

Topic: mechanism_design   Node: 0a7ebba0bb8d

arXiv:2606.22226, Theorem 4.5 (ratio form). For every prior, R_max(μ) ≤ (3/2) R_0(μ).
-/

open Finset in
/-- Marginals of a prior lie in `[0, 1]`. -/
lemma persuasion_marginal_mem_Icc {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : (ι → Bool) → ℝ) (hμ : is_bit_prior μ) (i : ι) :
    0 ≤ persuasion_marginal μ i ∧ persuasion_marginal μ i ≤ 1 := by
  constructor
  · exact sum_nonneg fun x _ => by split_ifs; exacts [hμ.1 x, le_refl 0]
  · rw [← hμ.2]
    exact sum_le_sum fun x _ => by split_ifs; exacts [le_refl _, hμ.1 x]

open Finset in
/-- Sender utility of the OR scheme: `∑_i (2 p_i - p_i²)`. -/
lemma persuasion_or_scheme_sender_utility {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : (ι → Bool) → ℝ) (hμ : is_bit_prior μ) :
    persuasion_sender_utility (persuasion_pair_or_scheme (fun x y => μ x * μ y)) =
      ∑ i, (2 * persuasion_marginal μ i - persuasion_marginal μ i ^ 2) := by
  classical
  rw [persuasion_pair_or_sender_utility]
  set p := persuasion_marginal μ
  let A : ι → (ι → Bool) → ℝ := fun i x => if x i = true then 1 else 0
  have hp : ∀ i, ∑ x, μ x * A i x = p i := by
    intro i; simp only [p, persuasion_marginal, A]
    apply sum_congr rfl; intro x _; split_ifs <;> simp
  calc ∑ x, ∑ y, μ x * μ y * ((Finset.univ.filter (fun i => (x i || y i) = true)).card : ℝ)
      = ∑ x, ∑ y, ∑ i, ((μ x * A i x) * μ y + μ x * (μ y * A i y) -
          (μ x * A i x) * (μ y * A i y)) := by
        apply sum_congr rfl; intro x _; apply sum_congr rfl; intro y _
        rw [natCast_card_filter, mul_sum]; apply sum_congr rfl; intro i _
        simp only [A]
        cases x i <;> cases y i <;> simp
    _ = ∑ x, ∑ i, ∑ y, ((μ x * A i x) * μ y + μ x * (μ y * A i y) -
          (μ x * A i x) * (μ y * A i y)) := sum_congr rfl (fun x _ => sum_comm)
    _ = ∑ i, ∑ x, ∑ y, ((μ x * A i x) * μ y + μ x * (μ y * A i y) -
          (μ x * A i x) * (μ y * A i y)) := sum_comm
    _ = ∑ i, (2 * p i - p i ^ 2) := by
        apply sum_congr rfl; intro i _
        simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum, ← sum_mul]
        rw [hp i, hμ.2]
        ring

open Finset in
/-- **arXiv:2606.22226, Theorem 4.5 (ratio form).** For every prior, `R_max(μ) ≤ (3/2) R_0(μ)`. -/
theorem persuasion_max_receiver_utility_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : (ι → Bool) → ℝ) (hμ : is_bit_prior μ) :
    persuasion_max_receiver_utility μ ≤ 3 / 2 * persuasion_prior_utility μ := by
  classical
  have hp := persuasion_marginal_mem_Icc μ hμ
  set p := persuasion_marginal μ
  have hobs := persuasion_pair_or_scheme_obedient μ (fun x y => μ x * μ y)
    (fun x y => mul_nonneg (hμ.1 x) (hμ.1 y)) (fun x y => mul_comm _ _)
    (fun x => by rw [← mul_sum, hμ.2, mul_one])
  have hSor := persuasion_or_scheme_sender_utility μ hμ
  have hR0 : 0 ≤ persuasion_prior_utility μ :=
    sum_nonneg fun i _ => le_max_of_le_left (hp i).1
  have key : ∀ q, is_sender_optimal_scheme μ q →
      persuasion_receiver_utility q ≤ 3 / 2 * persuasion_prior_utility μ := by
    rintro q ⟨hq, hopt⟩
    have h1 := persuasion_receiver_add_sender_le μ hμ.2 q hq
    have h2 := hopt _ hobs
    rw [hSor] at h2
    have hc : (Fintype.card ι : ℝ) = ∑ _i : ι, (1 : ℝ) := by simp
    have h3 : (Fintype.card ι : ℝ) + ∑ i, p i - ∑ i, (2 * p i - p i ^ 2) ≤
        3 / 2 * persuasion_prior_utility μ := by
      rw [hc, persuasion_prior_utility, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
      apply sum_le_sum; intro i _
      obtain ⟨h0, h1⟩ := hp i
      rcases le_total (p i) (1 - p i) with h | h
      · rw [max_eq_right h]; nlinarith
      · rw [max_eq_left h]; nlinarith
    linarith
  apply Real.sSup_le
  · rintro r ⟨q, hq, rfl⟩
    exact key q hq
  · positivity

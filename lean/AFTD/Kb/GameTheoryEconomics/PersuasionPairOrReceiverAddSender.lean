import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PersuasionReceiverUtility
import AFTD.Kb.GameTheoryEconomics.PersuasionPairOrScheme
import AFTD.Kb.GameTheoryEconomics.PersuasionSenderUtility
import AFTD.Kb.GameTheoryEconomics.PersuasionMarginal
import AFTD.Kb.GameTheoryEconomics.PersuasionPairOrSenderUtility

/-!
# persuasion_pair_or_receiver_add_sender

Topic: mechanism_design   Node: 19a5cd30090b

A pair-OR scheme never recommends 0 on a coordinate equal to 1, so the trade-off of Lemma 4.2 is an equality for it.
-/

open Finset in
/-- A pair-OR scheme never recommends `0` on a coordinate equal to `1`, so the trade-off of
Lemma 4.2 is an equality for it. -/
lemma persuasion_pair_or_receiver_add_sender {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : (ι → Bool) → ℝ) (hμ : ∑ x, μ x = 1) (ν : (ι → Bool) → (ι → Bool) → ℝ)
    (hνμ : ∀ x, ∑ y, ν x y = μ x) :
    persuasion_receiver_utility (persuasion_pair_or_scheme ν) +
        persuasion_sender_utility (persuasion_pair_or_scheme ν) =
      Fintype.card ι + ∑ i, persuasion_marginal μ i := by
  classical
  have hc : (Fintype.card ι : ℝ) = ∑ _i : ι, (1 : ℝ) := by simp
  have pt : ∀ x y : ι → Bool,
      ((Finset.univ.filter (fun i => (x i || y i) = x i)).card : ℝ) +
        ((Finset.univ.filter (fun i => (x i || y i) = true)).card : ℝ) =
      Fintype.card ι + ((Finset.univ.filter (fun i => x i = true)).card : ℝ) := by
    intro x y
    rw [hc, natCast_card_filter, natCast_card_filter, natCast_card_filter, ← sum_add_distrib,
      ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    cases x i <;> cases y i <;> norm_num
  have hR : persuasion_receiver_utility (persuasion_pair_or_scheme ν) =
      ∑ x, ∑ y, ν x y * ((Finset.univ.filter (fun i => (x i || y i) = x i)).card : ℝ) := by
    unfold persuasion_receiver_utility persuasion_pair_or_scheme
    apply sum_congr rfl; intro x _
    simp only [sum_mul]
    rw [sum_comm]
    apply sum_congr rfl; intro y _
    simp only [ite_mul, zero_mul]
    rw [sum_ite_eq]
    simp
  rw [hR, persuasion_pair_or_sender_utility, ← sum_add_distrib]
  have : ∀ x, ∑ y, ν x y * ((Finset.univ.filter (fun i => (x i || y i) = x i)).card : ℝ) +
      ∑ y, ν x y * ((Finset.univ.filter (fun i => (x i || y i) = true)).card : ℝ) =
      μ x * ((Fintype.card ι : ℝ) + ((Finset.univ.filter (fun i => x i = true)).card : ℝ)) := by
    intro x
    rw [← sum_add_distrib, ← hνμ x, sum_mul]
    apply sum_congr rfl; intro y _
    rw [← mul_add, pt]
  rw [sum_congr rfl (fun x _ => this x)]
  simp only [mul_add, sum_add_distrib]
  rw [← sum_mul, hμ, one_mul]
  congr 1
  unfold persuasion_marginal
  simp only [natCast_card_filter, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl; intro i _
  apply sum_congr rfl; intro x _
  split_ifs <;> simp

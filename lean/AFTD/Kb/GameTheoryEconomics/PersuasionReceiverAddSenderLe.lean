import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsObedientDirectScheme
import AFTD.Kb.GameTheoryEconomics.PersuasionReceiverUtility
import AFTD.Kb.GameTheoryEconomics.PersuasionSenderUtility
import AFTD.Kb.GameTheoryEconomics.PersuasionMarginal

/-!
# persuasion_receiver_add_sender_le

Topic: mechanism_design   Node: 476870526a55

Sender–receiver trade-off (Lemma 4.2). R(q) + S(q) ≤ n + ∑_i p_i(μ).
-/

open Finset in
/-- **Sender–receiver trade-off (Lemma 4.2).** `R(q) + S(q) ≤ n + ∑_i p_i(μ)`. -/
lemma persuasion_receiver_add_sender_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : (ι → Bool) → ℝ) (hμ : ∑ x, μ x = 1) (q : (ι → Bool) → (ι → Bool) → ℝ)
    (hq : is_obedient_direct_scheme μ q) :
    persuasion_receiver_utility q + persuasion_sender_utility q ≤
      Fintype.card ι + ∑ i, persuasion_marginal μ i := by
  classical
  have hc : (Fintype.card ι : ℝ) = ∑ _i : ι, (1 : ℝ) := by simp
  have pt : ∀ x a : ι → Bool, ((Finset.univ.filter (fun i => a i = x i)).card : ℝ) +
      ((Finset.univ.filter (fun i => a i = true)).card : ℝ) ≤
      Fintype.card ι + ((Finset.univ.filter (fun i => x i = true)).card : ℝ) := by
    intro x a
    rw [hc, natCast_card_filter, natCast_card_filter, natCast_card_filter, ← sum_add_distrib,
      ← sum_add_distrib]
    apply sum_le_sum
    intro i _
    cases a i <;> cases x i <;> norm_num
  have h1 : persuasion_receiver_utility q + persuasion_sender_utility q
      = ∑ x, ∑ a, q x a * (((Finset.univ.filter (fun i => a i = x i)).card : ℝ) +
          ((Finset.univ.filter (fun i => a i = true)).card : ℝ)) := by
    unfold persuasion_receiver_utility persuasion_sender_utility
    rw [← sum_add_distrib]
    apply sum_congr rfl; intro x _
    rw [← sum_add_distrib]
    apply sum_congr rfl; intro a _
    ring
  have h2 : ∑ x, ∑ a, q x a * (((Finset.univ.filter (fun i => a i = x i)).card : ℝ) +
          ((Finset.univ.filter (fun i => a i = true)).card : ℝ))
      ≤ ∑ x, ∑ a, q x a * ((Fintype.card ι : ℝ) +
          ((Finset.univ.filter (fun i => x i = true)).card : ℝ)) :=
    sum_le_sum fun x _ => sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (pt x a) (hq.1 x a)
  have h3 : ∑ x, ∑ a, q x a * ((Fintype.card ι : ℝ) +
          ((Finset.univ.filter (fun i => x i = true)).card : ℝ))
      = ∑ x, μ x * ((Fintype.card ι : ℝ) + ((Finset.univ.filter (fun i => x i = true)).card : ℝ)) := by
    apply sum_congr rfl; intro x _
    rw [← sum_mul, hq.2.1 x]
  have h4 : ∑ x, μ x * ((Fintype.card ι : ℝ) + ((Finset.univ.filter (fun i => x i = true)).card : ℝ))
      = Fintype.card ι + ∑ i, persuasion_marginal μ i := by
    simp only [mul_add, sum_add_distrib]
    rw [← sum_mul, hμ, one_mul]
    congr 1
    unfold persuasion_marginal
    simp only [natCast_card_filter, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl; intro i _
    apply sum_congr rfl; intro x _
    split_ifs <;> simp
  rw [h1, ← h4, ← h3]
  exact h2

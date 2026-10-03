import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsObedientDirectScheme
import AFTD.Kb.GameTheoryEconomics.PersuasionPairOrScheme
import AFTD.Kb.GameTheoryEconomics.PersuasionObedienceCost

/-!
# persuasion_pair_or_scheme_obedient

Topic: mechanism_design   Node: 7f87a53fce5a

The pair-OR scheme of a nonnegative symmetric coupling with first marginal μ is obedient.
-/

open Finset in
/-- The pair-OR scheme of a nonnegative symmetric coupling with first marginal `μ` is obedient. -/
lemma persuasion_pair_or_scheme_obedient {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : (ι → Bool) → ℝ) (ν : (ι → Bool) → (ι → Bool) → ℝ) (hν0 : ∀ x y, 0 ≤ ν x y)
    (hνs : ∀ x y, ν x y = ν y x) (hνμ : ∀ x, ∑ y, ν x y = μ x) :
    is_obedient_direct_scheme μ (persuasion_pair_or_scheme ν) := by
  classical
  refine ⟨fun x a => sum_nonneg fun y _ => ?_, fun x => ?_, fun a i => ?_⟩
  · split_ifs
    · exact hν0 x y
    · exact le_refl 0
  · unfold persuasion_pair_or_scheme
    rw [sum_comm, ← hνμ x]
    apply sum_congr rfl; intro y _
    rw [sum_ite_eq]
    simp
  · unfold persuasion_pair_or_scheme
    set L := ∑ x, (∑ y, if (fun i => x i || y i) = a then ν x y else 0) *
      persuasion_obedience_cost i x a
    have e1 : L = ∑ x, ∑ y, (if (fun i => x i || y i) = a then ν x y else 0) *
        persuasion_obedience_cost i x a := by
      simp only [L, sum_mul]
    have e2 : L = ∑ x, ∑ y, (if (fun i => x i || y i) = a then ν x y else 0) *
        persuasion_obedience_cost i y a := by
      rw [e1, sum_comm]
      apply sum_congr rfl; intro y _
      apply sum_congr rfl; intro x _
      have hor : (fun i => y i || x i) = (fun i => x i || y i) := by
        funext j; exact Bool.or_comm _ _
      rw [hor, hνs y x]
    have e3 : 2 * L ≤ 0 := by
      have : 2 * L = ∑ x, ∑ y, (if (fun i => x i || y i) = a then ν x y else 0) *
          (persuasion_obedience_cost i x a + persuasion_obedience_cost i y a) := by
        rw [two_mul]
        nth_rewrite 1 [e1]
        rw [e2, ← sum_add_distrib]
        apply sum_congr rfl; intro x _
        rw [← sum_add_distrib]
        apply sum_congr rfl; intro y _
        ring
      rw [this]
      apply sum_nonpos; intro x _
      apply sum_nonpos; intro y _
      split_ifs with h
      · apply mul_nonpos_of_nonneg_of_nonpos (hν0 x y)
        have hai : a i = (x i || y i) := by rw [← h]
        unfold persuasion_obedience_cost
        cases hx : x i <;> cases hy : y i <;> rw [hx, hy] at hai <;> simp [hai] <;> norm_num
      · simp
    linarith

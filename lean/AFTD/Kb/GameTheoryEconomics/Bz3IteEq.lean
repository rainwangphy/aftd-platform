import AFTD.Prelude

/-!
# bz3_ite_eq

Topic: general_equilibrium   Node: 9dd01e18baec

An if-then-else on a conjunction of decidable propositions, written as a product with a Boolean indicator.
-/

lemma bz3_ite_eq (A B : Prop) [Decidable A] [Decidable B] (c : ℝ) :
    (if ¬ A ∧ B then c else 0) = c * ((!decide A && decide B).toNat : ℝ) := by
  by_cases hA : A <;> by_cases hB : B <;> simp [hA, hB]

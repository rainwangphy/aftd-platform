import AFTD.Prelude

/-!
# is_bit_prior

Topic: mechanism_design   Node: 98b2e55d6ded

A probability distribution on {0,1}^ι.
-/

open Finset in
/-- A probability distribution on `{0,1}^ι`. -/
def is_bit_prior {ι : Type*} [Fintype ι] [DecidableEq ι] (μ : (ι → Bool) → ℝ) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ ∑ x, μ x = 1

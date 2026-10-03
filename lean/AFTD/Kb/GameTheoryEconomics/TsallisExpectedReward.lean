import AFTD.Prelude

/-!
# tsallis_expected_reward

Topic: mechanism_design   Node: b3127245afd6

The Tsallis expected reward with natural parameter gamma: the sum of x_k^gamma.
-/

def tsallis_expected_reward {n : ℕ} (γ : ℕ) (x : Fin n → ℝ) : ℝ :=
  ∑ k, x k ^ γ

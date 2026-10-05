import AFTD.Prelude

/-!
# fse_Anonymous

Topic: mechanism_design   Node: 1d6b02610ce7

Anonymity: permuting the agents' labels does not change the outcome.
-/

/-- Anonymity: permuting the agents' labels does not change the outcome. -/
def fse_Anonymous {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (x : Fin n → ℝ), f (x ∘ σ) = f x

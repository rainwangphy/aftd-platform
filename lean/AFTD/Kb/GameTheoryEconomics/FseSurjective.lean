import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FseInDomain

/-!
# fse_Surjective

Topic: mechanism_design   Node: 6af92f1e68f4

Surjectivity (onto [0,1]).
-/

/-- Surjectivity (onto `[0,1]`). -/
def fse_Surjective {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ y ∈ Set.Icc (0 : ℝ) 1, ∃ x : Fin n → ℝ, fse_InDomain x ∧ f x = y

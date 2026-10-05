import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FseInDomain

/-!
# fse_MapsToDomain

Topic: mechanism_design   Node: a83c0ffff75f

A deterministic mechanism maps every profile in [0,1]^n to a facility location in [0,1].
-/

/-- A deterministic mechanism maps every profile in `[0,1]^n` to a facility location in `[0,1]`. -/
def fse_MapsToDomain {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x : Fin n → ℝ, fse_InDomain x → f x ∈ Set.Icc (0 : ℝ) 1

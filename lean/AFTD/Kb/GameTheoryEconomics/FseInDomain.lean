import AFTD.Prelude

/-!
# fse_InDomain

Topic: mechanism_design   Node: 2649c560464e

A location profile of n agents lies in the domain [0,1].
-/

/-- A location profile of `n` agents lies in the domain `[0,1]`. -/
def fse_InDomain {n : ℕ} (x : Fin n → ℝ) : Prop := ∀ i, x i ∈ Set.Icc (0 : ℝ) 1

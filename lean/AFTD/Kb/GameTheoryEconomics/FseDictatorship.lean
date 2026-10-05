import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FseInDomain

/-!
# fse_Dictatorship

Topic: mechanism_design   Node: 96982fe4de30

f is a dictatorship: some fixed agent always gets her own location.
-/

/-- `f` is a dictatorship: some fixed agent always gets her own location. -/
def fse_Dictatorship {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ i : Fin n, ∀ x : Fin n → ℝ, fse_InDomain x → f x = x i

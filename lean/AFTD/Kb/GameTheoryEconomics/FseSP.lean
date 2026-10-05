import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FseCost
import AFTD.Kb.GameTheoryEconomics.FseInDomain

/-!
# fse_SP

Topic: mechanism_design   Node: c272305fa941

Strategyproofness for the scaling function q: no agent can lower her scaled cost by misreporting her location (any misreport in [0,1]).
-/

/-- Strategyproofness for the scaling function `q`: no agent can lower her scaled cost by misreporting her location (any misreport in `[0,1]`). -/
def fse_SP {n : ℕ} (q : ℝ → ℝ) (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x : Fin n → ℝ, fse_InDomain x → ∀ i : Fin n, ∀ x' : ℝ, x' ∈ Set.Icc (0 : ℝ) 1 →
    fse_cost q (f x) (x i) ≤ fse_cost q (f (Function.update x i x')) (x i)

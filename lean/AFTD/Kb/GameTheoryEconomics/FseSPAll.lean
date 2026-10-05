import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FseIsScaling
import AFTD.Kb.GameTheoryEconomics.FseSP

/-!
# fse_SPAll

Topic: mechanism_design   Node: 6de69cee27ea

A scaling-oblivious mechanism is strategyproof for *every* scaling function: the mechanism does not know q, and no agent can gain under any continuous positive q.
-/

/-- A scaling-oblivious mechanism is strategyproof for *every* scaling function: the mechanism does not know `q`, and no agent can gain under any continuous positive `q`. -/
def fse_SPAll {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ q : ℝ → ℝ, fse_IsScaling q → fse_SP q f

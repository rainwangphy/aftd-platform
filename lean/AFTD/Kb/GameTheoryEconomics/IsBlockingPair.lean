import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MarriageMarket

/-!
# is_blocking_pair

Topic: matching_markets   Node: 80c15dd36650

In a marriage market with agent types M and W and a matching μ : M ≃ W, a man m and a woman w form a blocking pair when m strictly prefers w to his assigned partner μ m, and w strictly prefers m to her assigned partner μ.symm w.
-/

/-- `m` and `w` block the matching `μ`: each strictly prefers the other to their assigned partner. -/
def is_blocking_pair {M W : Type*} (market : MarriageMarket M W)
    (μ : M ≃ W) (m : M) (w : W) : Prop :=
  market.pref_m m w (μ m) ∧ market.pref_w w m (μ.symm w)

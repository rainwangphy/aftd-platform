import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProportionalShareAlloc

/-!
# proportional_share_pay

Topic: mechanism_design   Node: 3e1b9dcd7d31

Proportional-share payment with total pool pool(W): identity j is paid its work share times pool(W).
-/

noncomputable def proportional_share_pay (pool : ℝ → ℝ) (bids : List ℝ) (j : ℕ) : ℝ :=
  proportional_share_alloc bids j * pool bids.sum

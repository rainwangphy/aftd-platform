import AFTD.Prelude
import AFTD.Kb.Tcs.OnlinePolicyValue
import AFTD.Kb.Tcs.RandomizedOMSRPolicy
import AFTD.Kb.Tcs.OMSRArrival

/-!
# expectedOnlineValue

Topic: online_algorithms   Node: 482ddcb550f5

Provenance: formalization of a published result. Source: scout/2611-03598-online-matching-with-arbitrary-stochastic-rewards.md:420

The expected total reward of a randomized online policy R on a list of arrivals arrs with weights w, defined as the integral over Ω of onlinePolicyValue w (R.policy ω) arrs univ with respect to R.μ.
-/

/-- Expected reward of a randomized online policy. -/
noncomputable def expectedOnlineValue {n : ℕ} (w : Fin n → ℝ)
    (R : RandomizedOMSRPolicy n) (arrs : List (OMSRArrival n)) : ℝ :=
  letI := R.mΩ
  letI := R.hμ
  MeasureTheory.integral R.μ (fun ω => onlinePolicyValue w (R.policy ω) arrs Finset.univ)

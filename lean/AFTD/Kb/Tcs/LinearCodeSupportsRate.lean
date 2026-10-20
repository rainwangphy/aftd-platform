import AFTD.Prelude
import AFTD.Kb.Tcs.CausalLinearNetworkCode
import AFTD.Kb.Tcs.CapacitatedNetwork
import AFTD.Kb.Tcs.UnicastSessions

/-!
# LinearCodeSupportsRate

Topic: information   Node: 026efb36959c

Provenance: formalization of a published result. Source: arXiv:2610.10108, Sec. 2

A common rate r is achievable by deterministic causal linear network coding over a field F on net with sessions sess if there exists a code : CausalLinearNetworkCode V K F net sess such that r ≤ (code.L : ℝ) / (code.T : ℝ).
-/

/-- Common rate r is achievable by a deterministic causal linear network code over field F. -/
def LinearCodeSupportsRate {V : Type} [Fintype V] [DecidableEq V] {K : Type} [Fintype K] [DecidableEq K]
    (F : Type) [Field F] (net : CapacitatedNetwork V) (sess : UnicastSessions V K) (r : ℝ) : Prop := ∃ code : CausalLinearNetworkCode V K F net sess, r ≤ (code.L : ℝ) / (code.T : ℝ)

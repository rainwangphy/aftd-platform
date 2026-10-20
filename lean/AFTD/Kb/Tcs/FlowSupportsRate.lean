import AFTD.Prelude
import AFTD.Kb.Tcs.IsMulticommodityFlow
import AFTD.Kb.Tcs.CapacitatedNetwork
import AFTD.Kb.Tcs.UnicastSessions

/-!
# FlowSupportsRate

Topic: information   Node: f6e0ad6ce536

Provenance: formalization of a published result. Source: arXiv:2610.10108, Sec. 2

A common rate r is supported by fractional multicommodity flow on a capacitated network net with unicast sessions sess if there exists a flow function f satisfying IsMulticommodityFlow net sess r f.
-/

/-- Common rate r is supported by fractional multicommodity flow on the capacitated network. -/
def FlowSupportsRate {V : Type} [Fintype V] [DecidableEq V] {K : Type} [Fintype K] [DecidableEq K]
    (net : CapacitatedNetwork V) (sess : UnicastSessions V K) (r : ℝ) : Prop := ∃ f, IsMulticommodityFlow net sess r f

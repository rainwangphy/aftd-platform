import AFTD.Prelude
import AFTD.Kb.Tcs.CapacitatedNetwork
import AFTD.Kb.Tcs.UnicastSessions
import AFTD.Kb.Tcs.FlowSupportsRate
import AFTD.Kb.Tcs.IsMulticommodityFlow

/-!
# flow_supports_rate_zero

Topic: information   Node: 4a9652830434

Provenance: helper lemma. folklore

On any capacitated network net with unicast sessions sess, the common rate zero is always supported by fractional multicommodity flow.
-/

/-- The zero common rate is always supported by fractional multicommodity flow. -/
theorem flow_supports_rate_zero {V : Type} [Fintype V] [DecidableEq V] {K : Type} [Fintype K] [DecidableEq K]
    (net : CapacitatedNetwork V) (sess : UnicastSessions V K) :
    FlowSupportsRate net sess 0 := by
  refine ⟨fun _ _ _ => 0, ?_, ?_, ?_⟩
  · intro k u v; simp
  · intro u v huv
    have hcap : 0 ≤ net.cap s(u, v) := by
      by_cases h : s(u, v) ∈ net.G.edgeSet
      · exact le_of_lt (net.cap_pos _ h)
      · rw [net.cap_zero _ h]
    simpa using hcap
  · intro k v
    simp

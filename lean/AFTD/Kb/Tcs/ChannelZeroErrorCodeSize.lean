import AFTD.Prelude
import AFTD.Kb.Tcs.DiscreteMemorylessChannel
import AFTD.Kb.Tcs.ChannelDistinguishabilityGraph
import AFTD.Kb.Tcs.SimpleGraphOrPower

/-!
# channel_zero_error_code_size

Topic: information   Node: 4891c608dfd1

Provenance: formalization of a published result. Source: arXiv:2610.41977, Section 5, Equation (5.1); Shannon 1956

The zero-error code size M_0(W, n) for a channel W in n channel uses is the clique number of the n-th OR-power of its distinguishability graph D(W).
-/

/-- The maximum number of zero-error messages in n uses of a channel W is the clique number of the n-th OR-power of its distinguishability graph. -/
noncomputable def channel_zero_error_code_size {A Y : Type*} [Fintype Y]
    (W : DiscreteMemorylessChannel A Y) (n : ℕ) : ℕ := (simple_graph_or_power (channel_distinguishability_graph W) n).cliqueNum

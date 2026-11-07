import AFTD.Prelude
import AFTD.Kb.Tcs.DiscreteMemorylessChannel
import AFTD.Kb.Tcs.ChannelDistinguishabilityGraph
import AFTD.Kb.Tcs.ShannonOrCapacity

/-!
# channel_zero_error_rate

Topic: information   Node: ed319129e543

Provenance: formalization of a published result. Source: arXiv:2610.41977, Section 5, Equation (5.1); Shannon 1956

The zero-error capacity rate R_0(W) of a channel W in bits per use is the base-2 logarithm of the Shannon OR-capacity of its distinguishability graph D(W).
-/

/-- The zero-error capacity rate in bits per use of a discrete memoryless channel W. -/
noncomputable def channel_zero_error_rate {A Y : Type*} [Fintype Y]
    (W : DiscreteMemorylessChannel A Y) : ℝ := Real.logb 2 (shannon_or_capacity (channel_distinguishability_graph W))

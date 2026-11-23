import AFTD.Prelude
import AFTD.Kb.Tcs.EdgeN

/-!
# WeightsN

Topic: quantum   Node: 582b68a930a3

Provenance: formalization of a published result. Source: arXiv:2611.26300

The type of edge-weight functions on a quantum graph on $N$ vertices with $D$ colours with values in $\alpha$.
-/

/-- Edge weights on a quantum graph. -/
abbrev WeightsN (N D : ℕ) (α : Type*) : Type _ := EdgeN N D → α

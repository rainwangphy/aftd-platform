import AFTD.Prelude
import AFTD.Kb.Tcs.SkewZeroForced

/-!
# skew_zero_forcing_closure

Topic: graphs   Node: 72105faa4f9c

Provenance: formalization of a published result. Source: arXiv:2611.15741 Section 1 and Section 2

The skew zero forcing closure scl(S) of a subset S of vertices in a graph with neighborhood function N is the set of all vertices forced by S under the skew color change rule.
-/

/-- The skew zero forcing closure of a vertex subset. -/
def skew_zero_forcing_closure {V : Type*} (N : V → Set V) (S : Set V) : Set V := {v | SkewZeroForced N S v}

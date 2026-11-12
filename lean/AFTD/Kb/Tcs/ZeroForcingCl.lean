import AFTD.Prelude
import AFTD.Kb.Tcs.ZeroForcingSeq

/-!
# zero_forcing_cl

Topic: graphs   Node: b23cd5ec0828

Provenance: formalization of a published result. Source: arXiv:2611.13244, Section 1 -- Stabilization of the zero forcing number of generalized Petersen graphs

The zero forcing closure cl(S) of a subset S of vertices in a simple graph G is the union over all natural numbers i of B_i.
-/

/-- The zero forcing closure of a subset S of vertices in a simple graph G, defined as the union of all B_i. -/
def zero_forcing_cl {V : Type*} (G : SimpleGraph V) (S : Set V) : Set V := ⋃ i : ℕ, zero_forcing_seq G S i

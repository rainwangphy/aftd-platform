import AFTD.Prelude
import AFTD.Kb.Tcs.IsZeroForcingSet

/-!
# is_connected_forcing_set

Topic: graphs   Node: 840849b90f02

Provenance: formalization of a published result. Source: arXiv:2611.11352 Section 1

A connected forcing set is a zero forcing set that induces a connected subgraph.
-/

/-- A zero forcing set that induces a connected subgraph. -/
def is_connected_forcing_set {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop := is_zero_forcing_set G S ∧ (G.induce S).Connected

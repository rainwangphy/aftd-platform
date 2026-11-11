import AFTD.Prelude
import AFTD.Kb.Tcs.IsZeroForcingSet

/-!
# is_total_forcing_set

Topic: graphs   Node: 20ea902174d0

Provenance: formalization of a published result. Source: arXiv:2611.11352 Section 1

A total forcing set is a zero forcing set that induces a subgraph with no isolated vertices.
-/

/-- A zero forcing set that induces a subgraph with no isolated vertices. -/
def is_total_forcing_set {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop := is_zero_forcing_set G S ∧ ∀ v : S, ∃ w : S, G.Adj v.1 w.1

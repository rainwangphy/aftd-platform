import AFTD.Prelude

/-!
# graph_has_no_indep_six

Topic: combinatorics   Node: 963b07c4d856

Provenance: formalization of a published result. Source: scout/2610-24484-erd-h-o-s-gy-arf-as-balanced-five-colorings.md:1267

A simple graph has no independent set of size 6 if every 6-element subset of vertices contains two distinct adjacent vertices.
-/

/-- A graph has no independent set of size 6 if every 6 vertices span at least one edge. -/
def graph_has_no_indep_six {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V, S.card = 6 → ∃ v ∈ S, ∃ w ∈ S, G.Adj v w

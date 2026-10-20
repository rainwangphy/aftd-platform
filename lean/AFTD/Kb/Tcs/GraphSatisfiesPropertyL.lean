import AFTD.Prelude
import AFTD.Kb.Tcs.EdgesOrdWithin

/-!
# graph_satisfies_property_l

Topic: combinatorics   Node: 8fdf335ee7c0

Provenance: formalization of a published result. Source: scout/2610-24484-erd-h-o-s-gy-arf-as-balanced-five-colorings.md:1275

A simple graph satisfies property (L) if every 6-element subset of vertices spans at most 22 directed edges.
-/

/-- Property (L): every 6 vertices span at most 11 undirected edges (at most 22 directed edges). -/
def graph_satisfies_property_l {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ S : Finset V, S.card = 6 → edges_ord_within G S ≤ 22

import AFTD.Prelude

/-!
# ve_comp_part

Topic: graphs   Node: 6eda601e6a52

Provenance: helper lemma. step towards not_is_fix_v0_of_neighbors_unreachable

The vertex set, inside V, of a connected component of the vertex-deleted subgraph G - v.
-/

/-- The set of vertices of `G` that lie in the connected component `C` of `G - v`. -/
def ve_comp_part {V : Type*} (G : SimpleGraph V) (v : V)
    (C : (G.induce ({v}ᶜ : Set V)).ConnectedComponent) : Set V := Subtype.val '' (C.supp : Set ↥({v}ᶜ : Set V))

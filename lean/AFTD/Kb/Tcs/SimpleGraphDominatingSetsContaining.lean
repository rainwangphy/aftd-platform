import AFTD.Prelude

/-!
# simple_graph_dominating_sets_containing

Topic: graphs   Node: c4bb0ef8e820

Provenance: formalization of a published result. Source: arXiv:2610.11446 (On the local average order of dominating sets), Sec. 1 (dominating sets; D_v(G)).

D_v(G): the dominating sets of G that contain v, where S dominates G when every vertex is in S or adjacent to a vertex of S.
-/

/-- `𝒟_v(G)`: the dominating sets of `G` that contain the vertex `v` (a set `S` dominates `G` when every vertex is in `S` or adjacent to a vertex of `S`). -/
def simple_graph_dominating_sets_containing {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : Finset (Finset V) :=
  Finset.univ.filter (fun S => v ∈ S ∧ ∀ w, w ∈ S ∨ ∃ u ∈ S, G.Adj u w)

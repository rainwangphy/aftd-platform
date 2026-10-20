import AFTD.Prelude

/-!
# simple_graph_dominating_sets

Topic: graphs   Node: 5700d8ad0cd4

Provenance: helper lemma. step towards simple_graph_local_avg_dominating_order_stem_le

D(G): the dominating sets of G, i.e. the finite vertex sets S such that every vertex of G lies in S or is adjacent to a vertex of S.
-/

/-- The family of all dominating sets of G; `simple_graph_dominating_sets_containing G v` is the subfamily of those containing v. -/
def simple_graph_dominating_sets {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Finset (Finset V) := Finset.univ.filter (fun S => ∀ w, w ∈ S ∨ ∃ u ∈ S, G.Adj u w)

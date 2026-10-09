import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphDominatingSetsContaining

/-!
# simple_graph_local_avg_dominating_order

Topic: graphs   Node: d088f0e995d6

Provenance: formalization of a published result. Source: arXiv:2610.11446 (On the local average order of dominating sets), Sec. 1 (avd_v(G) = Σ_{S ∈ D_v(G)} |S| / |D_v(G)|).

avd_v(G): the local average order of dominating sets containing v, i.e. the average size of the dominating sets of G that contain v.
-/

/-- `avd_v(G)`: the local average order of dominating sets containing `v`, the average size of the dominating sets of `G` that contain `v`. -/
def simple_graph_local_avg_dominating_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) : ℚ :=
  (∑ S ∈ simple_graph_dominating_sets_containing G v, (S.card : ℚ)) /
    (simple_graph_dominating_sets_containing G v).card

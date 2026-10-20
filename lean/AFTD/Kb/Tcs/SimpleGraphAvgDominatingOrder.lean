import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphDominatingSets

/-!
# simple_graph_avg_dominating_order

Topic: graphs   Node: 4d501b6ba391

Provenance: helper lemma. step towards simple_graph_local_avg_dominating_order_stem_le

avd(G): the global average order of dominating sets of G, i.e. the average size of all dominating sets of G. This is the quantity of Beaton--Cameron, related to the local quantity avd_v(G) by the leaf recursion.
-/

/-- avd(G): the global average order of the dominating sets of G, the average size of *all* dominating sets (not just those through a fixed vertex). -/
def simple_graph_avg_dominating_order {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℚ := (∑ S ∈ simple_graph_dominating_sets G, (S.card : ℚ)) / (simple_graph_dominating_sets G).card

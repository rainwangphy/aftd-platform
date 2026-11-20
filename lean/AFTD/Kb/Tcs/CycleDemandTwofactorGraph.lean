import AFTD.Prelude
import AFTD.Kb.Tcs.CycleDemandTwofactorGraphEdges

/-!
# cycle_demand_twofactor_graph

Topic: graphs   Node: 2e133a07a268

Provenance: helper lemma. Periodic two-factor local-state construction for the OP-874 campaign.

The base graph formed by two factor permutations and the matching.
-/

def cycle_demand_twofactor_graph {X : Type*} [Fintype X] [DecidableEq X]
    (sigma p : X ≃ X) : SimpleGraph (X × Bool) := SimpleGraph.fromEdgeSet (↑(cycle_demand_twofactor_graph_edges sigma p) : Set (Sym2 (X × Bool)))

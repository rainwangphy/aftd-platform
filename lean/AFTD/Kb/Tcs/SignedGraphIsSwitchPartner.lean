import AFTD.Prelude
import AFTD.Kb.Tcs.SignedGraphSwitch
import AFTD.Kb.Tcs.SignedGraphIsIsomorphic
import AFTD.Kb.Tcs.SignedGraph
import AFTD.Kb.Tcs.SignedGraphSameDeck

/-!
# SignedGraph.IsSwitchPartner

Topic: combinatorics   Node: ffd9997442c1

Provenance: helper lemma. step towards signed_graph_reconstructible_of_all_nonneg_net_degrees

A vertex w distinct from v is a switch partner of v in G if switching G at v and then at w is not isomorphic to G but has the same switching deck as G.
-/

/-- Switch partner of a vertex: the double switch at v and w is a non-isomorphic deck-mate. -/
def SignedGraph.IsSwitchPartner {V : Type*} [DecidableEq V] [Fintype V] (G : SignedGraph V) (v w : V) : Prop := v ≠ w ∧ ¬ SignedGraph.IsIsomorphic G ((G.switch v).switch w) ∧ G.SameDeck ((G.switch v).switch w)

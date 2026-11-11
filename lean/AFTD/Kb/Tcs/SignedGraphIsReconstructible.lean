import AFTD.Prelude
import AFTD.Kb.Tcs.SignedGraph
import AFTD.Kb.Tcs.SignedGraphIsIsomorphic
import AFTD.Kb.Tcs.SignedGraphSameDeck

/-!
# SignedGraph.IsReconstructible

Topic: combinatorics   Node: e2dc83781db0

Provenance: formalization of a published result. Source: arXiv:2611.13901, Sec. 2.2

A signed graph G on a finite type V with decidable equality is reconstructible from its switching deck if every signed graph G' on a finite type V' with decidable equality that has the same switching deck as G is isomorphic to G.
-/

/-- A signed graph is reconstructible if every signed graph with the same switching deck is isomorphic to it. -/
def SignedGraph.IsReconstructible {V : Type*} [DecidableEq V] [Fintype V] (G : SignedGraph V) : Prop :=
  ∀ {V' : Type*} [DecidableEq V'] [Fintype V'] (G' : SignedGraph V'),
    SignedGraph.SameDeck G G' → SignedGraph.IsIsomorphic G G'

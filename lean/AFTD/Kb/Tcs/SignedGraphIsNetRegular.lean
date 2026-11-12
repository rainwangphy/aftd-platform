import AFTD.Prelude
import AFTD.Kb.Tcs.SignedGraph
import AFTD.Kb.Tcs.SignedGraphNetDegree

/-!
# SignedGraph.IsNetRegular

Topic: combinatorics   Node: 35b088f91ca9

Provenance: formalization of a published result. Source: arXiv:2611.13901 Section 3.2

A signed graph G on a finite vertex set V is net-regular if there exists an integer d such that every vertex v of G has net-degree equal to d.
-/

/-- A signed graph is net-regular if all vertices have the same net-degree. -/
def SignedGraph.IsNetRegular {V : Type*} [Fintype V] (G : SignedGraph V) : Prop := ∃ d : ℤ, ∀ v : V, G.netDegree v = d

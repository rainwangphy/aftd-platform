import AFTD.Prelude
import AFTD.Kb.Tcs.SignedGraph

/-!
# SignedGraph.IsIsomorphic

Topic: combinatorics   Node: d9db98313901

Provenance: formalization of a published result. Source: arXiv:2611.13901, Sec. 2.1

Two signed graphs G1 and G2 are isomorphic if there is an isomorphism f between their underlying simple graphs that preserves the signs of all edges.
-/

/-- Isomorphism of signed graphs preserving edge signs. -/
def SignedGraph.IsIsomorphic {V1 V2 : Type*} (G1 : SignedGraph V1) (G2 : SignedGraph V2) : Prop :=
  ∃ (f : G1.graph ≃g G2.graph),
    ∀ (u v : V1) (h : G1.graph.Adj u v),
      G2.sgn ⟨s(f u, f v), f.map_adj_iff.mpr h⟩ = G1.sgn ⟨s(u, v), h⟩

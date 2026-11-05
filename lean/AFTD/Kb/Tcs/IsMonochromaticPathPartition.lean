import AFTD.Prelude
import AFTD.Kb.Tcs.IsMonochromaticPath

/-!
# is_monochromatic_path_partition

Topic: graphs   Node: c81e55d2e0da

Provenance: formalization of a published result. Source: arXiv:2611.06362 Section 1

A collection P of finite vertex sets is a monochromatic path partition of a finite simple graph G with edge colouring c : G.edgeSet → C if the sets in P are pairwise disjoint, their union is Finset.univ, and every set in P is a monochromatic path in G under c.
-/

/-- Predicate asserting that a family of vertex subsets partitions the vertex set into vertex-disjoint monochromatic paths. -/
def is_monochromatic_path_partition {V C : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) (c : G.edgeSet → C) (P : Finset (Finset V)) : Prop :=
  (P : Set (Finset V)).PairwiseDisjoint id ∧ P.biUnion id = Finset.univ ∧
    ∀ s ∈ P, is_monochromatic_path G c s

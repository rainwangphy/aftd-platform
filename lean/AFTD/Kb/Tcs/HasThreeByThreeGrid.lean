import AFTD.Prelude

/-!
# has_three_by_three_grid

Topic: combinatorics   Node: efca494b51ed

Provenance: formalization of a published result. Source: arXiv:2611.05261 Section 1 and Section 3

For a hypergraph with edge set H : Set (Finset V) of finite subsets of V, H contains a 3x3 grid if there exist families R, C : Fin 3 → Finset V of edges in H such that R is pairwise disjoint, C is pairwise disjoint, and ¬ Disjoint (R i) (C j) for all i, j : Fin 3.
-/

/-- Predicate that a hypergraph of finite edges contains a 3x3 grid of edges. -/
def has_three_by_three_grid {V : Type*} (H : Set (Finset V)) : Prop := ∃ (R C : Fin 3 → Finset V),
    (∀ i, R i ∈ H) ∧
    (∀ j, C j ∈ H) ∧
    (∀ i i', i ≠ i' → Disjoint (R i) (R i')) ∧
    (∀ j j', j ≠ j' → Disjoint (C j) (C j')) ∧
    (∀ i j, ¬ Disjoint (R i) (C j))

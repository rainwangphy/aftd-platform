import AFTD.Prelude

/-!
# has_cooperative_coloring_pair

Topic: combinatorics   Node: c19afe3d87c9

Provenance: formalization of a published result. Source: arXiv:2611.34299 Section 1

Two simple graphs on a common vertex set admit a cooperative coloring if there exist independent sets in each graph whose union covers the vertex set.
-/

/-- Two graphs on a common vertex set admit a cooperative coloring if there exist independent sets in each graph whose union covers the vertex set. -/
def has_cooperative_coloring_pair {V : Type*} (G₁ G₂ : SimpleGraph V) : Prop := ∃ I₁ I₂ : Set V, G₁.IsIndepSet I₁ ∧ G₂.IsIndepSet I₂ ∧ I₁ ∪ I₂ = Set.univ

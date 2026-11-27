import AFTD.Prelude

/-!
# has_cooperative_coloring_triple

Topic: combinatorics   Node: 1d202c13c939

Provenance: formalization of a published result. Source: arXiv:2611.34299, Section 1

Three simple graphs G₁, G₂, G₃ on a common vertex set V admit a cooperative 3-coloring if there exists a partition of V into three pairwise disjoint sets I₁, I₂, I₃ such that each Iᵢ is an independent set in Gᵢ.
-/

/-- Cooperative 3-coloring of three simple graphs as a partition into independent sets. -/
def has_cooperative_coloring_triple {V : Type*} (G₁ G₂ G₃ : SimpleGraph V) : Prop := ∃ I₁ I₂ I₃ : Set V, G₁.IsIndepSet I₁ ∧ G₂.IsIndepSet I₂ ∧ G₃.IsIndepSet I₃ ∧
    Disjoint I₁ I₂ ∧ Disjoint I₁ I₃ ∧ Disjoint I₂ I₃ ∧ I₁ ∪ I₂ ∪ I₃ = Set.univ

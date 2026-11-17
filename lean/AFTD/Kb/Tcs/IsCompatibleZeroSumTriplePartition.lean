import AFTD.Prelude

/-!
# is_compatible_zero_sum_triple_partition

Topic: combinatorics   Node: 2aeb0f24519f

Provenance: formalization of a published result. Source: arXiv:2611.18059 Section 1

A collection P of finite subsets of an additive Abelian group Γ is an h-compatible zero-sum partition into triples if every element of Γ belongs to a unique block in P, every block T in P has cardinality 3, the sum of elements in each block T in P is 0, and for every block T in P and every x in T, x + h does not belong to T.
-/

/-- An h-compatible zero-sum partition of an additive Abelian group into triples. -/
def is_compatible_zero_sum_triple_partition {Γ : Type*} [AddCommGroup Γ]
    (h : Γ) (P : Set (Finset Γ)) : Prop :=
  (∀ x : Γ, ∃! T ∈ P, x ∈ T) ∧
  (∀ T ∈ P, T.card = 3) ∧
  (∀ T ∈ P, ∑ x ∈ T, x = 0) ∧
  (∀ T ∈ P, ∀ x ∈ T, x + h ∉ T)

import AFTD.Prelude

/-!
# is_perfect_set

Topic: combinatorics   Node: bf9eb9f42831

Provenance: formalization of a published result. Source: arXiv:2611.07118, Perfect Partitions of Regular Bipartite Graphs, Section 1.1

A perfect set of order n is a finite set of n - 1 permutations of Fin n that are derangements and pairwise mutually deranged.
-/

/-- A perfect set of order n: a set of n - 1 pairwise mutually deranged derangements of Fin n. -/
def is_perfect_set (n : ℕ) (S : Finset (Equiv.Perm (Fin n))) : Prop := S.card = n - 1 ∧
  (∀ σ ∈ S, σ ∈ derangements (Fin n)) ∧
  ∀ ⦃σ⦄, σ ∈ S → ∀ ⦃τ⦄, τ ∈ S → σ ≠ τ → ∀ x, σ x ≠ τ x

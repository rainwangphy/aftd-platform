import AFTD.Prelude

/-!
# IsFactorizationCoarsening

Topic: combinatorics   Node: f17660aa1276

Provenance: formalization of a published result. Source: arXiv:2611.18194 (The Möbius function of factorizations with a simple prime factor), Definition 2 (coarsenings; exponent vectors replaced by the integers they encode, sums by products)

A multiset y is a coarsening of a multiset x of positive integers if x can be partitioned into nonempty groups so that y is the multiset of the products of the groups (the multiplicative form of Definition 2 of arXiv:2611.18194).
-/

/-- `y` is a coarsening of `x`: `x` is partitioned into nonempty groups (`G`, whose union is `x`) and each group is replaced by the product of its members. For factorizations of `n` this is the refinement order: `x ≤ y` when `y` is a coarsening of `x`. -/
def IsFactorizationCoarsening (x y : Multiset ℕ) : Prop :=
  ∃ G : Multiset (Multiset ℕ), (∀ g ∈ G, g ≠ 0) ∧ G.join = x ∧ G.map Multiset.prod = y

import AFTD.Prelude

/-!
# is_t_intersecting_partition_family

Topic: combinatorics   Node: 75417da8ef92

Provenance: formalization of a published result. Source: arXiv:2610.01747, Section 1, p. 3

Given natural numbers n and t, a finite set F of partitions of n (of type Finset (Nat.Partition n)) is t-intersecting if for every pair of partitions p, q in F, the size of the multiset intersection of their parts is at least t, that is, t ≤ (p.parts ∩ q.parts).card.
-/

/-- A family of partitions of n is t-intersecting if any two members have at least t common parts, counted with multiplicity. -/
def is_t_intersecting_partition_family {n : ℕ} (t : ℕ) (F : Finset (Nat.Partition n)) : Prop := ∀ p ∈ F, ∀ q ∈ F, t ≤ (p.parts ∩ q.parts).card

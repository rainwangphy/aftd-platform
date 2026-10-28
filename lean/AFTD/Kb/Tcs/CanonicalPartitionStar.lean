import AFTD.Prelude

/-!
# canonical_partition_star

Topic: combinatorics   Node: 537764f8b445

Provenance: formalization of a published result. Source: arXiv:2610.01747, Section 1, Eq. (132)

For natural numbers n and t, the canonical t-star canonical_partition_star n t is the finite set (of type Finset (Nat.Partition n)) of all partitions p of n such that t ≤ p.parts.count 1.
-/

/-- The canonical t-star T_{n, t} consists of all partitions of n containing at least t ones. -/
def canonical_partition_star (n t : ℕ) : Finset (Nat.Partition n) := Finset.univ.filter fun p => t ≤ p.parts.count 1

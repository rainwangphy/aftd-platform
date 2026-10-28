import AFTD.Prelude

/-!
# partition_A

Topic: combinatorics   Node: 0fb694ba6820

Provenance: formalization of a published result. Source: arXiv:2610.01747, Section 6.1, Eq. (23)

The family A_n of partitions of n consists of those partitions of n whose multiset of parts contains {1, 2}, {1, 3}, {1, 4}, or {2, 3, 4}.
-/

/-- The family A_n of integer partitions of n whose parts contain at least one member of H = {{1,2}, {1,3}, {1,4}, {2,3,4}}. -/
def partition_A (n : ℕ) : Finset (Nat.Partition n) := Finset.univ.filter fun p =>
    (1 ∈ p.parts ∧ 2 ∈ p.parts) ∨
    (1 ∈ p.parts ∧ 3 ∈ p.parts) ∨
    (1 ∈ p.parts ∧ 4 ∈ p.parts) ∨
    (2 ∈ p.parts ∧ 3 ∈ p.parts ∧ 4 ∈ p.parts)

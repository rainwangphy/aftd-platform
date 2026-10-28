import AFTD.Prelude

/-!
# partition_number

Topic: combinatorics   Node: 55b75f471b1e

Provenance: formalization of a published result. Source: arXiv:2610.01747 Section 6.1

The function partition_number maps an integer m : ℤ to an integer in ℤ: if 0 ≤ m, it returns the cardinality Nat.card of the type of partitions of m.toNat (Nat.Partition m.toNat) coerced to ℤ; otherwise (if m < 0), it returns 0.
-/

/-- The unrestricted integer partition function p(m), mapping ℤ to ℤ, with p(m) = 0 for m < 0. -/
noncomputable def partition_number (m : ℤ) : ℤ := if 0 ≤ m then (Nat.card (Nat.Partition m.toNat) : ℤ) else 0

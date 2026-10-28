import AFTD.Prelude

/-!
# partition_lift_57

Topic: combinatorics   Node: 3628cb4165bd

Provenance: formalization of a published result. Source: arXiv:2610.01747, Section 6.1, line 1392

For t ≥ 1, the lifting map sends a partition p of 57 to a partition of t + 56 by adding t - 1 ones to its multiset of parts.
-/

/-- Lifting a partition of 57 to a partition of t + 56 by adding t - 1 ones. -/
def partition_lift_57 (t : ℕ) (ht : 1 ≤ t) (p : Nat.Partition 57) : Nat.Partition (t + 56) := {
  parts := p.parts + Multiset.replicate (t - 1) 1
  parts_pos := by
    intro i hi
    rw [Multiset.mem_add] at hi
    rcases hi with hi | hi
    · exact p.parts_pos hi
    · obtain ⟨_, rfl⟩ := Multiset.eq_of_mem_replicate hi
      omega
  parts_sum := by
    simp [p.parts_sum]
    omega
}

import AFTD.Prelude
import AFTD.Kb.Tcs.OrderedSetPartition

/-!
# ordered_set_partition_single

Topic: combinatorics   Node: d13e4688cb54

Provenance: formalization of a published result. Source: arXiv:2611.34537 Section 1

For any natural number n, the ordered set partition of Fin (n + 1) whose list of blocks consists solely of the universal set Finset.univ.
-/

/-- The single-block ordered set partition of Fin (n + 1). -/
def ordered_set_partition_single (n : ℕ) : OrderedSetPartition (Fin (n + 1)) where
  blocks := [Finset.univ]
  nonempty_blocks := by
    intro B hB
    simp only [List.mem_singleton] at hB
    subst hB
    exact Finset.univ_nonempty
  pairwise_disjoint := by simp
  union_eq := by simp

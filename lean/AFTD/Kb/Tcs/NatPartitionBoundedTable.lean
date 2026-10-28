import AFTD.Prelude
import AFTD.Kb.Tcs.NatPartitionBoundedRowStep

/-!
# nat_partition_bounded_table

Topic: combinatorics   Node: 0a9251a64335

Provenance: helper lemma. step towards strict_counterexample_family_canonical_star_bound

The dynamic-programme table for bounded partition counts: the k-th row is the list of counts of partitions of 0,1,...,N with all parts at most k, built row by row from the row for k-1; row 0 is 1,0,0,...,0 (only the empty partition has all parts at most 0).
-/

def nat_partition_bounded_table : ℕ → ℕ → List ℕ := fun N k => match k with
    | 0 => 1 :: List.replicate N 0
    | (k + 1) => nat_partition_bounded_row_step (k + 1) (nat_partition_bounded_table N k)

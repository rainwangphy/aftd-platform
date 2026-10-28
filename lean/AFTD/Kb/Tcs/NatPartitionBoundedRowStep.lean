import AFTD.Prelude

/-!
# nat_partition_bounded_row_step

Topic: combinatorics   Node: b447dd567d4a

Provenance: helper lemma. step towards strict_counterexample_family_canonical_star_bound

One layer of the partition-counting dynamic programme: from the list of counts of partitions of 0,1,...,N by parts at most i-1, produce the list of counts of partitions by parts at most i, using the fibre sum over the number j of copies of the part i.
-/

def nat_partition_bounded_row_step (i : ℕ) (prev : List ℕ) : List ℕ := (List.range prev.length).map (fun m => ∑ j ∈ Finset.range (m / i + 1), prev.getD (m - j * i) 0)

import AFTD.Prelude

/-!
# nat_partition_bounded_count

Topic: combinatorics   Node: c26f10919573

Provenance: helper lemma. step towards strict_counterexample_family_canonical_star_bound

The number of partitions of m all of whose parts are at most k. Equivalently, the number of partitions of m into parts of size at most k.
-/

def nat_partition_bounded_count (k m : ℕ) : ℕ := Fintype.card {p : Nat.Partition m // ∀ x ∈ p.parts, x ≤ k}

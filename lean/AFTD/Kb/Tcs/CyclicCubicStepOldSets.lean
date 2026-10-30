import AFTD.Prelude

/-!
# cyclic_cubic_step_old_sets

Topic: quantum   Node: c682963f349a

Provenance: helper lemma. step towards cyclic_cubic_family_is_parity_repr

For T ⊆ {0,...,n-1} not containing n, the discrepancy between the level n+1 and level n moment counts is the sum of the indicators of T ⊆ S over these eight boundary sets S ⊆ {0,1,n-2,n-1}.
-/

/-- The eight boundary sets controlling the n to n+1 moment step in the case n not in T. -/
def cyclic_cubic_step_old_sets (n : ℕ) : Finset (Finset ℕ) := {{1}, {0, 1}, {n - 2}, {n - 2, n - 1}, {0, n - 2}, {1, n - 1}, {0, 1, n - 1}, {0, n - 2, n - 1}}

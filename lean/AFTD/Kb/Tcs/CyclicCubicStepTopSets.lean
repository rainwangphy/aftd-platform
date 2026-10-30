import AFTD.Prelude

/-!
# cyclic_cubic_step_top_sets

Topic: quantum   Node: e2bda9733f4d

Provenance: helper lemma. step towards cyclic_cubic_family_is_parity_repr

The discrepancy between the level n+1 moment count of insert n T and the level n moment count of T is the sum of the indicators of T ⊆ S over these five sets S ⊆ {0,1,n-2,n-1}.
-/

/-- The five boundary sets controlling the n to n+1 moment step in the case n in T. -/
def cyclic_cubic_step_top_sets (n : ℕ) : Finset (Finset ℕ) := {{1}, {0, 1}, {n - 2}, {0, n - 1}, {n - 2, n - 1}}

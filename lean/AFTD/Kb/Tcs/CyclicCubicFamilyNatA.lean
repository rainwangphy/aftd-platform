import AFTD.Prelude

/-!
# cyclic_cubic_family_nat_A

Topic: quantum   Node: 4bae19f0a28e

Provenance: helper lemma. step towards cyclic_cubic_family_is_parity_repr

The ten boundary parities (group A) of the cyclic cubic family, as Finsets of naturals: {1}, {0,1}, {n-3}, {0,n-2}, {n-3,n-2}, {1,n-1}, {0,1,n-1}, {n-4,n-1}, {n-4,n-3,n-1}, {0,n-2,n-1}.
-/

/-- Group A (10 boundary parities) of the Nat-level cyclic cubic family. -/
def cyclic_cubic_family_nat_A (n : ℕ) : Finset (Finset ℕ) := {{1}, {0, 1}, {n - 3}, {0, n - 2}, {n - 3, n - 2}, {1, n - 1}, {0, 1, n - 1}, {n - 4, n - 1}, {n - 4, n - 3, n - 1}, {0, n - 2, n - 1}}

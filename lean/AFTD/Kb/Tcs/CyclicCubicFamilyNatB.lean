import AFTD.Prelude

/-!
# cyclic_cubic_family_nat_B

Topic: quantum   Node: 356dcb7896c8

Provenance: helper lemma. step towards cyclic_cubic_family_is_parity_repr

The 2(n-4) running parities (group B): for each k <= n-5, the two parities {k} ∪ [k+3,n) and {k,k+1} ∪ [k+3,n).
-/

/-- Group B (2(n-4) running parities) of the Nat-level cyclic cubic family. -/
def cyclic_cubic_family_nat_B (n : ℕ) : Finset (Finset ℕ) := (Finset.Iic (n - 5)).biUnion fun k => let tail := Finset.Ico (k + 3) n; {insert k tail, insert k (insert (k + 1) tail)}

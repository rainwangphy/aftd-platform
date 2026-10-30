import AFTD.Prelude

/-!
# cyclic_cubic_family_nat_C

Topic: quantum   Node: 9d513ce6b475

Provenance: helper lemma. step towards cyclic_cubic_family_is_parity_repr

The three span parities (group C): [2,n), {0} ∪ [2,n) and [0,n).
-/

/-- Group C (3 span parities) of the Nat-level cyclic cubic family. -/
def cyclic_cubic_family_nat_C (n : ℕ) : Finset (Finset ℕ) := {Finset.Ico 2 n, insert 0 (Finset.Ico 2 n), Finset.Iio n}

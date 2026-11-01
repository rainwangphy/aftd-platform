import AFTD.Prelude

/-!
# odd_majority_sign

Topic: information   Node: 927bdec1122b

Provenance: helper lemma. step towards antipodal_hellinger_sharp_stability_majority_transition

The sign of the strict majority of n bits: odd_majority_sign n x = -1 if strictly more than half of the coordinates of x are true, and +1 otherwise. At n = 3 it coincides with majority_three.
-/

open scoped BigOperators in
/-- The n-bit majority sign, with the same convention as majority_three: -1 when strictly more than half the bits are true. -/
def odd_majority_sign (n : ℕ) : (Fin n → Bool) → ℝ := fun x ↦ if 2 * (∑ i : Fin n, (if x i then 1 else 0) : ℕ) > n then -1 else 1

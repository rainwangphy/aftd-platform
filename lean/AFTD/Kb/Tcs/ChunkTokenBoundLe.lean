import AFTD.Prelude

/-!
# chunk_token_bound_le

Topic: approximation   Node: b4a36c9d5e6e

Provenance: helper lemma. arXiv:2611.15074, Lemma 3.8 proof

For 2 ≤ q ≤ M, the number of chunks q is at most q - 1 + ⌈M / q⌉.
-/

/-- Arithmetic inequality q ≤ q - 1 + ⌈M / q⌉ for Case 1 of Lemma 3.8. -/
theorem chunk_token_bound_le (M q : ℕ) (hq : 2 ≤ q) (hqM : q ≤ M) :
    q ≤ q - 1 + M ⌈/⌉ q := by
  have hqpos : 0 < q := by omega
  have h1 : M ≤ q * (M ⌈/⌉ q) := by
    simpa using le_smul_ceilDiv (a := q) (b := M) hqpos
  have hc : 1 ≤ M ⌈/⌉ q := by
    have : q * 1 ≤ q * (M ⌈/⌉ q) := by omega
    exact Nat.le_of_mul_le_mul_left this hqpos
  calc q = q - 1 + 1 := (Nat.sub_add_cancel (by omega : 1 ≤ q)).symm
    _ ≤ q - 1 + M ⌈/⌉ q := Nat.add_le_add_left hc _

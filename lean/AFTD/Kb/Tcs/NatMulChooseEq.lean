import AFTD.Prelude

/-!
# nat_mul_choose_eq

Topic: combinatorics   Node: f3070e587cf4

Provenance: helper lemma. folklore

For natural numbers d and m with 1 ≤ m, m * Nat.choose d m = d * Nat.choose (d - 1) (m - 1).
-/

/-- Absorption identity for binomial coefficients: m * (d choose m) = d * (d-1 choose m-1). -/
theorem nat_mul_choose_eq {d m : ℕ} (hm : 1 ≤ m) :
    m * Nat.choose d m = d * Nat.choose (d - 1) (m - 1) := by
  have h := Nat.choose_mul (n := d) (k := m) (s := 1) hm
  simp only [Nat.choose_one_right] at h
  rwa [mul_comm] at h

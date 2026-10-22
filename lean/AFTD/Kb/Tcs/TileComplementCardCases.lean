import AFTD.Prelude

/-!
# tile_complement_card_cases

Topic: combinatorics   Node: 8e083d2e505f

Provenance: helper lemma. arXiv:2610.24022

Let d ≥ 3. If two natural numbers e_card and t_card satisfy e_card * t_card = 2^d and 2^(d - 3) ≤ e_card, then t_card equals 1, 2, 4, or 8.
-/

/-- Cardinality cases for the complement of a translational tile of size at least 2^(d-3). -/
theorem tile_complement_card_cases (d : ℕ) (hd : 3 ≤ d)
    (e_card t_card : ℕ) (hprod : e_card * t_card = 2 ^ d) (hbound : 2 ^ (d - 3) ≤ e_card) :
    t_card = 1 ∨ t_card = 2 ∨ t_card = 4 ∨ t_card = 8 := by
  have hdvd : t_card ∣ 2 ^ d := Dvd.intro_left e_card hprod
  obtain ⟨k, hk, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have h1 : 2 ^ (d - 3) * 2 ^ k ≤ 2 ^ d := by
    calc 2 ^ (d - 3) * 2 ^ k ≤ e_card * 2 ^ k := Nat.mul_le_mul_right (2 ^ k) hbound
    _ = 2 ^ d := hprod
  have h2 : 2 ^ d = 2 ^ (d - 3) * 8 := by
    have hd3 : d = (d - 3) + 3 := (Nat.sub_add_cancel hd).symm
    rw [hd3, pow_add]
    rfl
  rw [h2] at h1
  have hpos : 0 < 2 ^ (d - 3) := Nat.two_pow_pos (d - 3)
  have hle : 2 ^ k ≤ 8 := Nat.le_of_mul_le_mul_left h1 hpos
  have hk3 : k ≤ 3 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hle
  interval_cases k <;> decide

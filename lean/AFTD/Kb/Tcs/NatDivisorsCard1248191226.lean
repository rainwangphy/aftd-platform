import AFTD.Prelude

/-!
# nat_divisors_card_1248191226

Topic: graphs   Node: 53ef357f9713

Provenance: helper lemma. step towards op_652_half_degree_packing_negation

The number of divisors of 1248191226 is 36.
-/

/-- The number of positive divisors of 1248191226 = 18 * 37^5 is 36. -/
theorem nat_divisors_card_1248191226 : (Nat.divisors 1248191226).card = 36 := by
  rw [show 1248191226 = 18 * 37 ^ 5 by norm_num]
  rw [Nat.Coprime.card_divisors_mul (by decide)]
  have h37 : (Nat.divisors (37 ^ 5)).card = 6 := by
    rw [Nat.divisors_prime_pow (by norm_num : Nat.Prime 37)]
    simp
  have h18 : (Nat.divisors 18).card = 6 := by decide
  rw [h37, h18]

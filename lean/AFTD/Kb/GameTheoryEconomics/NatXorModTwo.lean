import AFTD.Prelude

/-!
# nat_xor_mod_two

Topic: combinatorial_games   Node: 7ed346cd41d6

Provenance: helper lemma. step towards spider_two_leg_one_free

For any natural numbers a and b, (a ^^^ b) % 2 = (a + b) % 2.
-/

/-- The bitwise XOR of natural numbers modulo 2 equals their sum modulo 2. -/
theorem nat_xor_mod_two (a b : ℕ) : (a ^^^ b) % 2 = (a + b) % 2 := Nat.xor_mod_two_eq

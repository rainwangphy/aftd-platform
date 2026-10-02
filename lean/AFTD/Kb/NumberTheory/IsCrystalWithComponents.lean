import AFTD.Prelude

/-!
# is_crystal_with_components

Topic: elementary_number_theory   Node: b0c60e1b084b

An odd number n is a crystal with components a and b if n = ab with a, b > 1 and 2(a+1)(b+1) divides (a+b)^2 + (ab+1)^2.
-/

/-- `n` is a crystal with components `a`, `b` (Abrate et al., arXiv:1601.03081): `n = ab` is odd, `a, b > 1`, and the biharmonic mean `((a+b)² + (ab+1)²) / (2(a+1)(b+1))` is an integer. -/
def is_crystal_with_components (n a b : ℕ) : Prop :=
  Odd n ∧ 1 < a ∧ 1 < b ∧ n = a * b ∧ 2 * (a + 1) * (b + 1) ∣ (a + b) ^ 2 + (a * b + 1) ^ 2

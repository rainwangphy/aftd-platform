import AFTD.Prelude

/-!
# binary_digit_sum

Topic: elementary_number_theory   Node: d48b4dcffd04

Provenance: formalization of a published result. Source: arXiv:2611.26953, Section 1.1

The sum of the digits in the binary representation of a natural number k.
-/

/-- The sum of the binary digits of a natural number. -/
def binary_digit_sum (k : ℕ) : ℕ := (Nat.digits 2 k).sum

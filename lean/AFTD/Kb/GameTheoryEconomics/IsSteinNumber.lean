import AFTD.Prelude

/-!
# is_stein_number

Topic: combinatorial_games   Node: 31918beaffa0

Provenance: formalization of a published result. Source: arXiv:2611.05898, Definition 1.3

A positive integer n is an E. P. Stein number if, with m = Nat.sqrt n, both n - m^2 and n + m^2 are positive squares.
-/

/-- Predicate asserting that n is a positive integer such that n - m^2 and n + m^2 are positive squares for m = Nat.sqrt n. -/
def is_stein_number (n : ℕ) : Prop :=
  0 < n ∧
  let m := Nat.sqrt n
  0 < n - m^2 ∧ IsSquare (n - m^2) ∧ 0 < n + m^2 ∧ IsSquare (n + m^2)

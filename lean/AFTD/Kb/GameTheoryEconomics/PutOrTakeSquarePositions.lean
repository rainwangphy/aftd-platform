import AFTD.Prelude

/-!
# PutOrTakeSquarePositions

Topic: combinatorial_games   Node: e3b92acf144d

Provenance: formalization of a published result. Source: arXiv:2611.05898 -- An Asymptotic for E. P. Stein Numbers

The set of positive integers $n$ such that both $n - \lfloor\sqrt{n}\rfloor^2$ and $n + \lfloor\sqrt{n}\rfloor^2$ are positive integer squares.
-/

/-- The set of positive integers n such that n - ⌊√n⌋² and n + ⌊√n⌋² are both positive squares. -/
def PutOrTakeSquarePositions : Set ℕ := {n : ℕ |
  0 < n ∧
  0 < n - (Nat.sqrt n)^2 ∧ IsSquare (n - (Nat.sqrt n)^2) ∧
  0 < n + (Nat.sqrt n)^2 ∧ IsSquare (n + (Nat.sqrt n)^2)}

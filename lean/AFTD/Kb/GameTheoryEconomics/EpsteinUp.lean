import AFTD.Prelude

/-!
# epstein_up

Topic: combinatorial_games   Node: 6e8f794a90c2

Provenance: formalization of a published result. Source: arXiv:2611.05898 Sec. 1

The up-move in Epstein's put-or-take-a-square game, defined as epstein_up n = n + (Nat.sqrt n)^2.
-/

/-- The up-move U(n) = n + ⌊√n⌋² in Epstein's put-or-take-a-square game. -/
def epstein_up (n : ℕ) : ℕ := n + (Nat.sqrt n)^2

import AFTD.Prelude

/-!
# epstein_down

Topic: combinatorial_games   Node: 1c47a9c9265a

Provenance: formalization of a published result. Source: arXiv:2611.05898 Sec. 1

The down-move in Epstein's put-or-take-a-square game, defined as epstein_down n = n - (Nat.sqrt n)^2.
-/

/-- The down-move D(n) = n - ⌊√n⌋² in Epstein's put-or-take-a-square game. -/
def epstein_down (n : ℕ) : ℕ := n - (Nat.sqrt n)^2

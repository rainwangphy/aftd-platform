import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SlowExactNimTruncationBound

/-!
# slow_exact_nim_truncate

Topic: combinatorial_games   Node: 4a8d6916b3ab

Provenance: formalization of a published result. Source: arXiv:2611.14546:182

The truncated position obtained from x on k+1 piles in slow exact k-Nim by capping each pile size x_i at the truncation bound slow_exact_nim_truncation_bound k x.
-/

/-- The truncated position y_i = min(x_i, L) in slow exact k-Nim with k+1 piles. -/
noncomputable def slow_exact_nim_truncate (k : ℕ) (x : Fin (k + 1) → ℕ) : Fin (k + 1) → ℕ := fun i => min (x i) (slow_exact_nim_truncation_bound k x)

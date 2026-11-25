import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Op2347G

/-!
# op2347_w

Topic: combinatorial_games   Node: af7efe92a7f5

Provenance: formalization of a published result. Source: arXiv:2611.31336

The win/loss outcome sequence (as a boolean function where true indicates a winning position and false indicates a losing position) for the subtraction game with move set {10, 12, 24, 72 * k - 1}.
-/

/-- The win/loss outcome sequence for subtraction game with moves {10, 12, 24, 72k - 1}. -/
noncomputable def op2347_w (k : ℕ) : ℕ → Bool := fun n => decide (op2347_g k n ≠ 0)

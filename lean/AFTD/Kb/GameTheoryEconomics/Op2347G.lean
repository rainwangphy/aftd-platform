import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SubtractionGrundy

/-!
# op2347_g

Topic: combinatorial_games   Node: 4fc9d6b71a9e

Provenance: formalization of a published result. Source: arXiv:2611.31336

The Sprague-Grundy sequence for the normal-play subtraction game with move set {10, 12, 24, 72 * k - 1}.
-/

/-- The Sprague-Grundy sequence for subtraction game with moves {10, 12, 24, 72k - 1}. -/
noncomputable def op2347_g (k : ℕ) : ℕ → ℕ := subtraction_grundy {10, 12, 24, 72 * k - 1}

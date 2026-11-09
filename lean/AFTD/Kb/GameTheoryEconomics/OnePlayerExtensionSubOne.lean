import AFTD.Prelude

/-!
# one_player_extension_sub_one

Topic: equilibria   Node: 426ea9cdf0bd

Provenance: helper lemma. arXiv:2611.06076 Proposition 2.3 proof

For any real number α with 2 - α ≠ 0, 1 - 1 / (2 - α) = (1 - α) / (2 - α).
-/

/-- Algebraic rearrangement for one-player extension: subtracting the update from 1. -/
lemma one_player_extension_sub_one (α : ℝ) (hα : 2 - α ≠ 0) :
    1 - 1 / (2 - α) = (1 - α) / (2 - α) := by
  field_simp
  ring

import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnePlayerExtensionSubOne

/-!
# one_player_extension_reciprocal_step

Topic: equilibria   Node: 915a6b7c73a8

Provenance: helper lemma. arXiv:2611.06076 Proposition 2.3 proof

For any real number α with α < 1, 1 / (1 - 1 / (2 - α)) = 1 / (1 - α) + 1.
-/

/-- Reciprocal step for one-player extension: 1 / (1 - 1 / (2 - α)) = 1 / (1 - α) + 1. -/
lemma one_player_extension_reciprocal_step (α : ℝ) (hα : α < 1) :
    1 / (1 - 1 / (2 - α)) = 1 / (1 - α) + 1 := by
  have h2 : 2 - α ≠ 0 := by linarith
  have h1 : 1 - α ≠ 0 := by linarith
  rw [one_player_extension_sub_one α h2]
  field_simp
  ring

import AFTD.Prelude

/-!
# one_player_extension_theta_identity

Topic: equilibria   Node: d80d27c05b79

Provenance: helper lemma. arXiv:2611.06076 Lemma 2.1 proof

For any real α with 2 - α ≠ 0, setting θ = 1/(2-α) satisfies θα + 1 - θ = θ.
-/

/-- Regret balancing identity θ * α + (1 - θ) = θ for the one-player extension parameter. -/
theorem one_player_extension_theta_identity (α : ℝ) (hα : 2 - α ≠ 0) :
    (1 / (2 - α)) * α + (1 - (1 / (2 - α))) = 1 / (2 - α) := by
  field_simp
  ring

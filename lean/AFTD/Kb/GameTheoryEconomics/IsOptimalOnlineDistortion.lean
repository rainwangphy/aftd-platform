import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnlineICDecision
import AFTD.Kb.GameTheoryEconomics.IsOnlineDistortionBounded

/-!
# is_optimal_online_distortion

Topic: social_choice   Node: 8b3c8e64fe4a

Provenance: formalization of a published result. Source: arXiv:2611.30683 Sec. 3.1, Stay or Switch? Metric Distortion with Online Candidate Arrivals

For horizon T, is_optimal_online_distortion T D asserts that D is the infimum of metric distortions achievable by deterministic online IC rules: for every ε > 0 some rule achieves distortion at most D + ε, and every rule with distortion bound D' satisfies D ≤ D'.
-/

/-- The optimal deterministic metric distortion for horizon T is the infimum of distortions achieved by deterministic online IC rules. -/
def is_optimal_online_distortion (T : ℕ) (D : ℝ) : Prop := (∀ ε > 0, ∃ rule : OnlineICDecision T, is_online_distortion_bounded rule (D + ε)) ∧
  (∀ rule : OnlineICDecision T, ∀ D' : ℝ, is_online_distortion_bounded rule D' → D ≤ D')

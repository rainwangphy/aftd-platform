import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ScoringNormOne
import AFTD.Kb.GameTheoryEconomics.ScoringLast

/-!
# rank_score_veto_core_hall_condition

Topic: social_choice   Node: dec4d6ccefb7

Provenance: formalization of a published result. Source: arXiv:2610.26535 Lemma 5

For natural numbers m, n1, and n2, a hypothesis hm : 2 ≤ m, and a scoring function s : Fin m → ℚ, rank_score_veto_core_hall_condition m hm s n1 n2 is the proposition asserting that (n2 : ℚ) / (n1 + n2 : ℚ) ≤ ((n1 : ℚ) * (scoring_norm_one s - scoring_last m hm s) + (n2 : ℚ) * (scoring_norm_one s - 1)) / ((n1 + n2 : ℚ) * scoring_norm_one s).
-/

/-- The fractional matching inequality for candidate b1 in the 1D voter configuration. -/
def rank_score_veto_core_hall_condition (m : ℕ) (hm : 2 ≤ m) (s : Fin m → ℚ) (n₁ n₂ : ℕ) : Prop :=
  (n₂ : ℚ) / (n₁ + n₂ : ℚ) ≤
    ((n₁ : ℚ) * (scoring_norm_one s - scoring_last m hm s) + (n₂ : ℚ) * (scoring_norm_one s - 1)) /
      ((n₁ + n₂ : ℚ) * scoring_norm_one s)

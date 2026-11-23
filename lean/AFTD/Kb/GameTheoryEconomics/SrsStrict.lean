import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialRankingSolution
import AFTD.Kb.GameTheoryEconomics.PowerProfile

/-!
# srs_strict

Topic: social_choice   Node: 2cee27e2eab7

Provenance: formalization of a published result. Source: arXiv:2611.19021 Section 2.1

Individual x is strictly preferred to y under an SRS R at profile π if x is weakly preferred to y and y is not weakly preferred to x.
-/

/-- The asymmetric (strict preference) part of a social ranking solution. -/
def srs_strict {X : Type*} (R : SocialRankingSolution X) (π : PowerProfile X) (x y : X) : Prop := R.rel π x y ∧ ¬ R.rel π y x

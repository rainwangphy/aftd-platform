import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PowerRelation
import AFTD.Kb.GameTheoryEconomics.PowerProfile

/-!
# SocialRankingSolution

Topic: social_choice   Node: fdca9333b3f3

Provenance: formalization of a published result. Source: arXiv:2611.19021 Definition 1

A social ranking solution (SRS) maps each profile of power relations to a complete binary relation on the individuals.
-/

/-- A social ranking solution maps each profile of power relations to a complete binary relation on individuals. -/
structure SocialRankingSolution (X : Type*) where
  rel : PowerProfile X → X → X → Prop
  complete : ∀ (π : PowerProfile X) (x y : X), rel π x y ∨ rel π y x

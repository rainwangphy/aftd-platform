import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialRankingSolution
import AFTD.Kb.GameTheoryEconomics.PowerProfile
import AFTD.Kb.GameTheoryEconomics.IsMergingSumPowerProfile
import AFTD.Kb.GameTheoryEconomics.SrsStrict
import AFTD.Kb.GameTheoryEconomics.PowerRelation

/-!
# satisfies_con

Topic: social_choice   Node: c6eabdf13ad0

Provenance: formalization of a published result. Source: arXiv:2611.19021 Definition 5

An SRS R satisfies consistency (CON) if for all power profiles π₁, π₂, and π such that π₁.card = π₂.card and is_merging_sum_power_profile π π₁ π₂ holds, and for all individuals x and y: if R ranks x weakly above y at π₁ and at π₂, then R ranks x weakly above y at π; and if R strictly prefers x to y at π₁ and ranks x weakly above y at π₂, then R strictly prefers x to y at π.
-/

/-- Consistency (CON) for a social ranking solution. -/
def satisfies_con {X : Type*} (R : SocialRankingSolution X) : Prop := ∀ (π₁ π₂ π : PowerProfile X),
    π₁.card = π₂.card →
    is_merging_sum_power_profile π π₁ π₂ →
    ∀ x y : X,
      (R.rel π₁ x y → R.rel π₂ x y → R.rel π x y) ∧
      (srs_strict R π₁ x y → R.rel π₂ x y → srs_strict R π x y)

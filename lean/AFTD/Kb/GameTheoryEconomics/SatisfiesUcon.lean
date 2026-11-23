import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialRankingSolution
import AFTD.Kb.GameTheoryEconomics.PowerProfile
import AFTD.Kb.GameTheoryEconomics.SrsStrict
import AFTD.Kb.GameTheoryEconomics.PowerRelation

/-!
# satisfies_ucon

Topic: social_choice   Node: a96990133285

Provenance: formalization of a published result. Source: arXiv:2611.19021 Definition 6

An SRS satisfies union consistency (UCON) if whenever x is weakly preferred to y in two profiles π₁ and π₂, x is weakly preferred to y in their multiset sum π₁ + π₂, and if x is strictly preferred in π₁ and weakly preferred in π₂, then x is strictly preferred in π₁ + π₂.
-/

/-- Union consistency (UCON) for a social ranking solution. -/
def satisfies_ucon {X : Type*} (R : SocialRankingSolution X) : Prop := ∀ (π₁ π₂ : PowerProfile X) (x y : X),
    (R.rel π₁ x y → R.rel π₂ x y → R.rel (π₁ + π₂) x y) ∧
    (srs_strict R π₁ x y → R.rel π₂ x y → srs_strict R (π₁ + π₂) x y)

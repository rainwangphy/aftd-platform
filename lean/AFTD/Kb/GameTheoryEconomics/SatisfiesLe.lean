import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialRankingSolution
import AFTD.Kb.GameTheoryEconomics.PowerRelation
import AFTD.Kb.GameTheoryEconomics.LexCel
import AFTD.Kb.GameTheoryEconomics.PowerProfile

/-!
# satisfies_le

Topic: social_choice   Node: 4c3eb7b2dfd9

Provenance: formalization of a published result. Source: arXiv:2611.19021 Definition 8

An SRS R satisfies Lex-cel extension (LE) if for every power relation r and all individuals x and y, R.rel {r} x y holds if and only if lex_cel r x y holds.
-/

/-- Lex-cel extension (LE) for a social ranking solution. -/
def satisfies_le {X : Type*} [DecidableEq X] (R : SocialRankingSolution X) : Prop := ∀ (r : PowerRelation X) (x y : X),
    R.rel {r} x y ↔ lex_cel r x y

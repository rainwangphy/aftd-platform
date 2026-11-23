import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PowerRelation
import AFTD.Kb.GameTheoryEconomics.LexGe
import AFTD.Kb.GameTheoryEconomics.AppearanceVector

/-!
# lex_cel

Topic: social_choice   Node: 8a16354ac197

Provenance: formalization of a published result. Source: arXiv:2611.19021 Definition 7

For individuals x and y and a power relation r, x is weakly preferred to y under the Lex-cel solution at r, denoted lex_cel r x y, if lex_ge holds between the appearance vector of x in r and the appearance vector of y in r.
-/

/-- The Lex-cel solution on a single power relation. -/
def lex_cel {X : Type*} [DecidableEq X] (r : PowerRelation X) (x y : X) : Prop := lex_ge (appearance_vector r x) (appearance_vector r y)

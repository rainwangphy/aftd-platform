import AFTD.Prelude
import AFTD.Kb.Tcs.OppGloveSide
import AFTD.Kb.Tcs.Handshake

/-!
# handshake_right_side

Topic: combinatorics   Node: 5a996832e76a

Provenance: helper lemma. step towards glove_number_k5

The glove side directly touched by the second vertex of a handshake: in a single handshake $x|a\overline{a}|y$ the opposite side $\overline{a}$ touched by $y$, in a double handshake $x|a\overline{a}|\overline{b}b|y$ the side $b$ worn by $y$.
-/

/-- The glove side directly touched by the second vertex of a handshake. -/
def handshake_right_side {V Γ : Type*} : Handshake V Γ → Γ × Bool := fun h => match h with
  | .single _ a _ => opp_glove_side a
  | .double _ _ b _ => b

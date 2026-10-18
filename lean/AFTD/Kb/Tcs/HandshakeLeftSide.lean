import AFTD.Prelude
import AFTD.Kb.Tcs.Handshake

/-!
# handshake_left_side

Topic: combinatorics   Node: 339afadbc290

Provenance: helper lemma. step towards glove_number_k5

The glove side directly touched by the first vertex of a handshake: in a single handshake $x|a\overline{a}|y$ the side $a$ worn by $x$, in a double handshake $x|a\overline{a}|\overline{b}b|y$ the side $a$ worn by $x$.
-/

/-- The glove side directly touched by the first vertex of a handshake. -/
def handshake_left_side {V Γ : Type*} : Handshake V Γ → Γ × Bool := fun h => match h with
  | .single _ a _ => a
  | .double _ a _ _ => a

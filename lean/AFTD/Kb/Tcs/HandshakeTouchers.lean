import AFTD.Prelude
import AFTD.Kb.Tcs.OppGloveSide
import AFTD.Kb.Tcs.Handshake

/-!
# handshake_touchers

Topic: combinatorics   Node: 213e0b5ac6c8

Provenance: helper lemma. step towards glove_number_k4

The set of vertices that directly touch the glove side `s` during the handshake `h`: for a single handshake `x|a opp(a)|y` the vertex `x` touches `a` and `y` touches the opposite side; for a double handshake `x|a|b|y` the vertex `x` touches `a` and `y` touches `b`; every other side is untouched. (In a double handshake the two outer sides merely exchange contamination, they are not touched.)
-/

/-- The vertices that directly touch the glove side `s` during the handshake `h`. -/
def handshake_touchers {V : Type*} {Γ : Type*} [DecidableEq Γ] (h : Handshake V Γ) (s : Γ × Bool) : Set V := match h with
  | .single x a y => if s = a then {x} else if s = opp_glove_side a then {y} else ∅
  | .double x a b y => if s = a then {x} else if s = b then {y} else ∅

import AFTD.Prelude
import AFTD.Kb.Tcs.Handshake
import AFTD.Kb.Tcs.OppGloveSide

/-!
# handshake_update_contam

Topic: combinatorics   Node: b5417ef35792

Provenance: formalization of a published result. Source: scout/2610-17602-clean-handshake-sequences.md:176

The updated contamination map after a handshake: players add their germs to the glove sides they touch directly, and in a double handshake the outer sides of the two gloves share their contaminants.
-/

/-- Contamination update rule following a handshake. -/
def handshake_update_contam {V : Type*} {Γ : Type*} [DecidableEq Γ] (h : Handshake V Γ) (t : Γ × Bool → Set V) : Γ × Bool → Set V := fun s =>
    match h with
    | .single x a y =>
        if s = a then t a ∪ {x}
        else if s = opp_glove_side a then t (opp_glove_side a) ∪ {y}
        else t s
    | .double x a b y =>
        if s = a then t a ∪ {x}
        else if s = b then t b ∪ {y}
        else if s = opp_glove_side a ∨ s = opp_glove_side b then
          t (opp_glove_side a) ∪ t (opp_glove_side b)
        else t s

import AFTD.Prelude
import AFTD.Kb.Tcs.Handshake
import AFTD.Kb.Tcs.OppGloveSide

/-!
# handshake_is_clean

Topic: combinatorics   Node: 3fa20ac5e975

Provenance: formalization of a published result. Source: scout/2610-17602-clean-handshake-sequences.md:212

A handshake is clean with respect to a contamination map $t : \Gamma \times \mathrm{Bool} \to \mathrm{Set}(V)$ if no player directly touches a glove side containing contaminants from another player, and in a double handshake the two players wear distinct gloves.
-/

/-- Cleanliness condition for a handshake given contamination sets. -/
def handshake_is_clean {V : Type*} {Γ : Type*} (h : Handshake V Γ) (t : Γ × Bool → Set V) : Prop := match h with
  | .single x a y => t a ⊆ {x} ∧ t (opp_glove_side a) ⊆ {y}
  | .double x a b y => a.1 ≠ b.1 ∧ t a ⊆ {x} ∧ t b ⊆ {y}

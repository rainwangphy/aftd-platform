import AFTD.Prelude

/-!
# opp_glove_side

Topic: combinatorics   Node: 10f7f8beb73a

Provenance: formalization of a published result. Source: scout/2610-17602-clean-handshake-sequences.md:147

The opposite side of a glove side $(g, b)$ in $\Gamma \times \mathrm{Bool}$ is $(g, \neg b)$, representing the inside-out orientation of the same glove.
-/

/-- The opposite orientation of a glove side. -/
def opp_glove_side {Γ : Type*} (s : Γ × Bool) : Γ × Bool := (s.1, !s.2)

import AFTD.Prelude

/-!
# turn_is_alice

Topic: combinatorial_games   Node: 0a442720aed8

Provenance: formalization of a published result. Source: arXiv:2611.32746 Sec 1

Given a partial colouring c : V → Option Bool on a finite vertex type V, turn_is_alice c holds if and only if the number of coloured vertices (vertices v with (c v).isSome = true) is an even natural number.
-/

/-- Given a partial colouring c : V → Option Bool, it is Alice's turn when the number of coloured vertices is even. -/
def turn_is_alice {V : Type*} [Fintype V] (c : V → Option Bool) : Prop :=
  Even (Finset.univ.filter (fun v => (c v).isSome)).card

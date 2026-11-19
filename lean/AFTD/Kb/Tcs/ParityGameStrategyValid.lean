import AFTD.Prelude

/-!
# parity_game_strategy_valid

Topic: automata   Node: 5b5c925e22f6

Provenance: helper lemma. step towards parity_games_in_polynomial_time

A positional strategy σ : V → V for Even is legal (valid) when E u (σ u) = true at every vertex u owned by Even; only Even's own moves need to be checked, since at Odd-owned vertices the adversary may follow any edge.
-/

/-- Legality of a positional Even strategy: `E u (σ u)` holds at every Even-owned vertex `u`. -/
def parity_game_strategy_valid {V : Type} (own : V → Bool) (E : V → V → Bool) (σ : V → V) : Prop := ∀ u, own u = true → E u (σ u) = true

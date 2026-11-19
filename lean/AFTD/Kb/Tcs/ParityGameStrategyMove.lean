import AFTD.Prelude

/-!
# parity_game_strategy_move

Topic: automata   Node: a4adc1fb36ea

Provenance: helper lemma. step towards parity_games_in_polynomial_time

The move graph of a positional strategy: for a game on V with owner map own, edge relation E and positional strategy σ : V → V, `parity_game_strategy_move own E σ u w` says that w is a legal successor of u when Even follows σ: at an Even-owned vertex u the only move is to σ u, at an Odd-owned vertex u every E-successor is allowed.
-/

/-- The move relation of the graph induced by a positional strategy. -/
def parity_game_strategy_move {V : Type} (own : V → Bool) (E : V → V → Bool) (σ : V → V) (u w : V) : Prop := (own u = true ∧ w = σ u) ∨ (own u = false ∧ E u w = true)

import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickGameMoveZero

/-!
# pick_game_move_payoff

Topic: fair_division   Node: 30ce03de11e4

Provenance: helper lemma. Operational finite perfect-information picking game for arXiv:2611.09685 Section 7, OP-1323.

The mover’s additive payoff from the current remaining objects if the specified item is chosen, followed by the given continuations: agent 0 receives its candidate bundle, and agent 1 receives the remaining items outside it.
-/

noncomputable def pick_game_move_payoff {n : ℕ} (u : Fin 2 → Fin n → ℝ)
    (s : List (Fin 2)) (F : List (Fin n) → Finset (Fin n))
    (h : List (Fin n)) (x : Fin n) : ℝ := let p := s.getD h.length 0
  let R := Finset.univ \ h.toFinset
  let A := pick_game_move_zero s F h x
  ∑ z ∈ (if p = 0 then A else R \ A), u p z

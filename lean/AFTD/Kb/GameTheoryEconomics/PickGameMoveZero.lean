import AFTD.Prelude

/-!
# pick_game_move_zero

Topic: fair_division   Node: 128d8f44c3bf

Provenance: helper lemma. Operational finite perfect-information picking game for arXiv:2611.09685 Section 7, OP-1323.

For a history and a legal next choice, the resulting agent-0 continuation bundle consists of the selected object together with the subsequent continuation if agent 0 moves, and otherwise is the subsequent continuation.
-/

noncomputable def pick_game_move_zero {n : ℕ} (s : List (Fin 2))
    (F : List (Fin n) → Finset (Fin n)) (h : List (Fin n)) (x : Fin n) : Finset (Fin n) := if s.getD h.length 0 = 0 then insert x (F (h ++ [x])) else F (h ++ [x])

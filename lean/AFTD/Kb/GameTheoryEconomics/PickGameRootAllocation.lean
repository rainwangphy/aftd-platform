import AFTD.Prelude

/-!
# pick_game_root_allocation

Topic: fair_division   Node: afb008b72de2

Provenance: helper lemma. Operational finite perfect-information picking game for arXiv:2611.09685 Section 7, OP-1323.

The root allocation from the continuation assigns its root bundle to agent 0 and all remaining objects to agent 1.
-/

noncomputable def pick_game_root_allocation {n : ℕ} (F : List (Fin n) → Finset (Fin n))
    (i : Fin 2) : Finset (Fin n) := if i = 0 then F [] else Finset.univ \ F []

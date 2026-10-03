import AFTD.Prelude

/-!
# lxv_opt

Topic: fair_division   Node: 1bb1fbe9ec74

The allocation with bundles {g2,g3}, {g4}, {g1,g5}, {g6}.
-/

/-- The leximin-optimal EF1 allocation: bundles {g2,g3}, {g4}, {g1,g5}, {g6}. -/
def lxv_opt : Fin 6 → Fin 4 := ![2, 0, 0, 1, 2, 3]

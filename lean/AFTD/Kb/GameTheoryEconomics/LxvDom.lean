import AFTD.Prelude

/-!
# lxv_dom

Topic: fair_division   Node: 6dd506e350a3

The allocation with bundles {g2,g3}, {g5}, {g1,g4}, {g6} (agents 2 and 3 swap g4 and g5).
-/

/-- The allocation dominating it: agents 2 and 3 swap g4 and g5. -/
def lxv_dom : Fin 6 → Fin 4 := ![2, 0, 0, 2, 1, 3]

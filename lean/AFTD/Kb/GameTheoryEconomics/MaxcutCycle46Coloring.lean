import AFTD.Prelude

/-!
# maxcut_cycle46_coloring

Topic: equilibria   Node: 57303ff4bde7

Provenance: helper lemma. Explicit coloring sequence for maxcut_unweighted_strong_deviation_cycle_exists; experiment 12438.

The five successive three-color profiles of the 46-vertex example, with stage addition modulo five.
-/

def maxcut_cycle46_coloring (stage : Fin 5) (v : Fin 46) : Fin 3 :=
  if v.val < 8 then (if stage.val = 0 then 0 else 2)
  else if v.val < 16 then (if stage.val = 0 ∨ 3 ≤ stage.val then 1 else 0)
  else if v.val < 24 then (if stage.val = 0 ∨ 4 ≤ stage.val then 2 else 1)
  else if v.val < 32 then (if stage.val = 1 then 1 else 0)
  else if v.val < 39 then 1 else 2

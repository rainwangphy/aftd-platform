import AFTD.Prelude

/-!
# maxcut_cycle71_coloring

Topic: equilibria   Node: e65d559ff75e

Provenance: helper lemma. Explicit regular 71-vertex construction for the unweighted minimal-deviation cycle, supported by experiments 12443, 12444, 12450 and 12452.

Five displayed three-color profiles on the regular 71-vertex construction, with anchor colors fixed and four core blocks recolored in sequence.
-/

def maxcut_cycle71_coloring (stage : Fin 5) (v : Fin 71) : Fin 3 :=
  if v.val < 8 then (if stage.val = 0 then 0 else 2)
  else if v.val < 16 then (if stage.val = 0 ∨ 3 ≤ stage.val then 1 else 0)
  else if v.val < 24 then (if stage.val = 0 ∨ 4 ≤ stage.val then 2 else 1)
  else if v.val < 32 then (if stage.val = 1 then 1 else 0)
  else if v.val < 45 then 0 else if v.val < 58 then 1 else 2

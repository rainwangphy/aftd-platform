import AFTD.Prelude
import AFTD.Kb.Tcs.In715DeficitPSize

/-!
# in715_deficit_proper_row_7

Topic: graphs   Node: d69d1425981f

Provenance: helper lemma. Finite graph and certificates from experiments 20940 and 20968; see state/campaigns/triangle_reductions/outside_induced_kernel_in701.md.

Finite certificate for the explicit fourteen-vertex graph.
-/

open scoped Sym2
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
open In701Deficit14

theorem in715_deficit_proper_row_7 : ∀ v : Fin 14, G.Adj 7 v → s((7 : Fin 14),v) ∉ C → color 7 ≠ color v := by
  intro v
  fin_cases v <;> decide +kernel

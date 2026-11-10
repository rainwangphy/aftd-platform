import AFTD.Prelude
import AFTD.Kb.Tcs.In715DeficitPSize

/-!
# in715_deficit_proper_row_0

Topic: graphs   Node: 3240c66a5a53

Provenance: helper lemma. Finite graph and certificates from experiments 20940 and 20968; see state/campaigns/triangle_reductions/outside_induced_kernel_in701.md.

Finite certificate for the explicit fourteen-vertex graph.
-/

open scoped Sym2
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
open In701Deficit14

theorem in715_deficit_proper_row_0 : ∀ v : Fin 14, G.Adj 0 v → s((0 : Fin 14),v) ∉ C → color 0 ≠ color v := by
  intro v
  fin_cases v <;> decide +kernel

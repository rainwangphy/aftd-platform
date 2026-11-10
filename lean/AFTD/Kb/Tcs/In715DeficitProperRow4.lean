import AFTD.Prelude
import AFTD.Kb.Tcs.In715DeficitPSize

/-!
# in715_deficit_proper_row_4

Topic: graphs   Node: 4b7f8173bdce

Provenance: helper lemma. Finite graph and certificates from experiments 20940 and 20968; see state/campaigns/triangle_reductions/outside_induced_kernel_in701.md.

Finite certificate for the explicit fourteen-vertex graph.
-/

open scoped Sym2
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
open In701Deficit14

theorem in715_deficit_proper_row_4 : ∀ v : Fin 14, G.Adj 4 v → s((4 : Fin 14),v) ∉ C → color 4 ≠ color v := by
  intro v
  fin_cases v <;> decide +kernel

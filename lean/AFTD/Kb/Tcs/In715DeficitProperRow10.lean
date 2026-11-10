import AFTD.Prelude
import AFTD.Kb.Tcs.In715DeficitPSize

/-!
# in715_deficit_proper_row_10

Topic: graphs   Node: 825ea9c95eca

Provenance: helper lemma. Finite graph and certificates from experiments 20940 and 20968; see state/campaigns/triangle_reductions/outside_induced_kernel_in701.md.

Finite certificate for the explicit fourteen-vertex graph.
-/

open scoped Sym2
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
open In701Deficit14

theorem in715_deficit_proper_row_10 : ∀ v : Fin 14, G.Adj 10 v → s((10 : Fin 14),v) ∉ C → color 10 ≠ color v := by
  intro v
  fin_cases v <;> decide +kernel

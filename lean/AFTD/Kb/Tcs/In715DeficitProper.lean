import AFTD.Prelude
import AFTD.Kb.Tcs.In715DeficitPSize
import AFTD.Kb.Tcs.In715DeficitProperRow0
import AFTD.Kb.Tcs.In715DeficitProperRow1
import AFTD.Kb.Tcs.In715DeficitProperRow2
import AFTD.Kb.Tcs.In715DeficitProperRow3
import AFTD.Kb.Tcs.In715DeficitProperRow4
import AFTD.Kb.Tcs.In715DeficitProperRow5
import AFTD.Kb.Tcs.In715DeficitProperRow6
import AFTD.Kb.Tcs.In715DeficitProperRow7
import AFTD.Kb.Tcs.In715DeficitProperRow8
import AFTD.Kb.Tcs.In715DeficitProperRow9
import AFTD.Kb.Tcs.In715DeficitProperRow10
import AFTD.Kb.Tcs.In715DeficitProperRow11
import AFTD.Kb.Tcs.In715DeficitProperRow12
import AFTD.Kb.Tcs.In715DeficitProperRow13

/-!
# in715_deficit_proper

Topic: graphs   Node: 4a7a274ff9d4

Provenance: helper lemma. Finite graph and certificates from experiments 20940 and 20968; see state/campaigns/triangle_reductions/outside_induced_kernel_in701.md.

Finite certificate for the explicit fourteen-vertex graph.
-/

open scoped Sym2
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
open In701Deficit14

theorem in715_deficit_proper : ∀ u v : Fin 14, G.Adj u v → s(u,v) ∉ C → color u ≠ color v := by
  intro u
  fin_cases u
  · exact in715_deficit_proper_row_0
  · exact in715_deficit_proper_row_1
  · exact in715_deficit_proper_row_2
  · exact in715_deficit_proper_row_3
  · exact in715_deficit_proper_row_4
  · exact in715_deficit_proper_row_5
  · exact in715_deficit_proper_row_6
  · exact in715_deficit_proper_row_7
  · exact in715_deficit_proper_row_8
  · exact in715_deficit_proper_row_9
  · exact in715_deficit_proper_row_10
  · exact in715_deficit_proper_row_11
  · exact in715_deficit_proper_row_12
  · exact in715_deficit_proper_row_13

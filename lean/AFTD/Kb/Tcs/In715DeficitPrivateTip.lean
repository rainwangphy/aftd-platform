import AFTD.Prelude
import AFTD.Kb.Tcs.In715DeficitPSize

/-!
# in715_deficit_private_tip

Topic: graphs   Node: f5c9efdf7be0

Provenance: helper lemma. Finite graph and certificates from experiments 20940 and 20968; see state/campaigns/triangle_reductions/outside_induced_kernel_in701.md.

Finite certificate for the explicit fourteen-vertex graph.
-/

open scoped Sym2
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
open In701Deficit14

theorem in715_deficit_private_tip : ({0,4,9} : Finset (Fin 14)) ∈ P ∧
    ∀ t ∈ P, (9 : Fin 14) ∈ t → t = ({0,4,9} : Finset (Fin 14)) := by decide +kernel

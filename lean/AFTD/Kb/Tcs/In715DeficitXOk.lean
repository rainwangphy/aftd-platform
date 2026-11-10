import AFTD.Prelude
import AFTD.Kb.Tcs.In715DeficitPSize

/-!
# in715_deficit_x_ok

Topic: graphs   Node: a594009d1cac

Provenance: helper lemma. Finite graph and certificates from experiments 20940 and 20968; see state/campaigns/triangle_reductions/outside_induced_kernel_in701.md.

Finite certificate for the explicit fourteen-vertex graph.
-/

open scoped Sym2
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
open In701Deficit14

theorem in715_deficit_x_ok : X.card = 5 ∧ ∀ t ∈ X, G.IsNClique 3 t ∧ (10 : Fin 14) ∈ t := by decide +kernel

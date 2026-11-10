import AFTD.Prelude
import AFTD.Kb.Tcs.In715DeficitPSize

/-!
# in715_deficit_p_tri

Topic: graphs   Node: 3d1d66f7ea9b

Provenance: helper lemma. Finite graph and certificates from experiments 20940 and 20968; see state/campaigns/triangle_reductions/outside_induced_kernel_in701.md.

Finite certificate for the explicit fourteen-vertex graph.
-/

open scoped Sym2
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
open In701Deficit14

theorem in715_deficit_p_tri : ∀ t ∈ P, G.IsNClique 3 t := by
  intro t ht
  simp only [P, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

import AFTD.Prelude
import AFTD.Kb.Tcs.In715DeficitPSize

/-!
# in715_deficit_link_is_cycle

Topic: graphs   Node: 4ac6ab16256b

Provenance: helper lemma. Finite graph and certificates from experiments 20940 and 20968; see state/campaigns/triangle_reductions/outside_induced_kernel_in701.md.

Finite certificate for the explicit fourteen-vertex graph.
-/

open scoped Sym2
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem in715_deficit_link_is_cycle : ∀ u v : Fin 14,
    u ∈ ({0,1,2,3,4} : Finset (Fin 14)) →
    v ∈ ({0,1,2,3,4} : Finset (Fin 14)) →
    (In701Deficit14.G.Adj u v ↔ s(u,v) ∈
      ({s(0,1),s(1,2),s(2,3),s(3,4),s(0,4)} : Finset (Sym2 (Fin 14)))) := by
  decide +kernel

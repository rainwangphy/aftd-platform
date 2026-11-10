import AFTD.Prelude
import AFTD.Kb.Tcs.In715SharpWitnessCount
import AFTD.Kb.Tcs.SimpleGraphIn693TenSeedPackingNumber

/-!
# in715_Wcover1

Topic: graphs   Node: ea40cf5b8677

Provenance: helper lemma. Ten-vertex graph and pair-avoidance witnesses from experiments 20301–20303 and 20312; see state/campaigns/triangle_reductions/private_k4_in694.md.

Finite verification of the explicit ten-vertex packing and edge-avoidance witnesses.
-/

open scoped Sym2
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem in715_Wcover1 : ∀ e ∈ (sharp_EL.drop 5).take 5, ∀ f ∈ sharp_EL, ∃ q ∈ sharp_W, e ∈ q.1 ∧ f ∈ q.1 := by decide +kernel

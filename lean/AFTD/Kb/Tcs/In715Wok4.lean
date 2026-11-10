import AFTD.Prelude
import AFTD.Kb.Tcs.In715SharpWitnessCount
import AFTD.Kb.Tcs.SimpleGraphIn693TenSeedPackingNumber

/-!
# in715_Wok4

Topic: graphs   Node: d1453b9d13a4

Provenance: helper lemma. Ten-vertex graph and pair-avoidance witnesses from experiments 20301–20303 and 20312; see state/campaigns/triangle_reductions/private_k4_in694.md.

Finite verification of the explicit ten-vertex packing and edge-avoidance witnesses.
-/

open scoped Sym2
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem in715_Wok4 : ∀ q ∈ in715_W4, q.2.toFinset.card = 8 ∧ (∀ t ∈ q.2, t ∈ sharp_T) ∧ (∀ a ∈ q.2, ∀ b ∈ q.2, a ≠ b → (a ∩ b).card ≤ 1) ∧ (∀ e ∈ q.1, ∀ t ∈ q.2, e ∉ t.sym2) := by decide +kernel

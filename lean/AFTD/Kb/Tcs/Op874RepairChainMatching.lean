import AFTD.Prelude
import AFTD.Kb.Tcs.Op874RepairChainEnds

/-!
# op874_repair_chain_matching

Topic: graphs   Node: 81ce8220a95b

Provenance: helper lemma. step towards op874_repair_chain_data

The ten matching edges per block of the repair chain: the images of the endpoint indices twenty through twenty-nine.
-/

/-- The ten matching edges per block of the repair chain: the images of the endpoint indices twenty through twenty-nine. -/
def op874_repair_chain_matching (k : ℕ) [NeZero k] : Finset (Sym2 (Fin k × Fin 20)) := (Finset.univ.filter (fun e : Fin k × Fin 30 => 20 ≤ e.2.val)).image (op874_repair_chain_ends k)

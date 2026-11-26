import AFTD.Prelude
import AFTD.Kb.Tcs.Op874RepairBaseGraph
import AFTD.Kb.Tcs.Op874RepairBaseLeft
import AFTD.Kb.Tcs.Op874RepairBaseRight

/-!
# op874_repair_block_incidence

Topic: graphs   Node: 7d632331da27

Provenance: helper lemma. step towards op874_repair_chain_data

The number of internal block edges incident with port r.
-/

/-- The number of internal block edges incident with port r. -/
def op874_repair_block_incidence (r : Fin 20) : ℕ := (Finset.univ.filter (fun t : Fin 20 => op874_repair_base_graph.Adj r t)).card

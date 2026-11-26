import AFTD.Prelude
import AFTD.Kb.Tcs.Op874RepairBaseGraph
import AFTD.Kb.Tcs.Op874RepairBaseBit
import AFTD.Kb.Tcs.Op874RepairBaseLeft
import AFTD.Kb.Tcs.Op874RepairBaseRight

/-!
# op874_repair_block_cut_count

Topic: graphs   Node: 96285536ad84

Provenance: helper lemma. step towards op874_repair_chain_data

The number of non-matching block edges at port r whose other endpoint has the same matching-cut bit as r.
-/

/-- The number of non-matching block edges at port r whose other endpoint has the same matching-cut bit as r. -/
def op874_repair_block_cut_count (r : Fin 20) : ℕ := (Finset.univ.filter (fun t : Fin 20 => op874_repair_base_graph.Adj r t ∧
      op874_repair_base_bit t = op874_repair_base_bit r ∧
      ¬ (∃ j : Fin 30, 20 ≤ j.val ∧
        s(op874_repair_base_left j, op874_repair_base_right j) = s(r, t)))).card

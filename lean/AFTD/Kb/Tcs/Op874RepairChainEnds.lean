import AFTD.Prelude
import AFTD.Kb.Tcs.Op874RepairBaseLeft
import AFTD.Kb.Tcs.Op874RepairBaseRight

/-!
# op874_repair_chain_ends

Topic: graphs   Node: c7eb6a3c6484

Provenance: helper lemma. Saturated fixed-color repair obstruction for OP-874, https://arxiv.org/abs/2610.41950, Section 2.

Join consecutive twenty-vertex blocks across their matching ports 16 and 19, leaving all other edges inside their block.
-/

def op874_repair_chain_ends (k : ℕ) [NeZero k] : Fin k × Fin 30 → Sym2 (Fin k × Fin 20) := fun p => if p.2 = 29 then s((p.1,16),(p.1+1,19)) else s((p.1,op874_repair_base_left p.2),(p.1,op874_repair_base_right p.2))

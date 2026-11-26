import AFTD.Prelude
import AFTD.Kb.Tcs.Op874A
import AFTD.Kb.Tcs.Op874B
import AFTD.Kb.Tcs.Op874V

/-!
# op874IsMEdge

Topic: graphs   Node: cd86d963ab1d

Provenance: helper lemma. step towards op874_mixed_matching_overlap_gadget_chain

The eight matching edges of one block, listed as ordered pairs with the block index fixed; inter-block joins use i+1.
-/

/-- Ordered-pair description of the eight matching edges of one block: A2-A7, A6-A0, B1-B3, B5-B7 (intra), A1-B6, A5-B2 (cross-bit), A4-B0', A3-B4' (inter-block joins). -/
def op874IsMEdge {k : ℕ} [NeZero k] (u v : op874V k) : Prop := 
  ∃ i : Fin k,
    (u = op874A i 2 ∧ v = op874A i 7) ∨
    (u = op874A i 6 ∧ v = op874A i 0) ∨
    (u = op874B i 1 ∧ v = op874B i 3) ∨
    (u = op874B i 5 ∧ v = op874B i 7) ∨
    (u = op874A i 1 ∧ v = op874B i 6) ∨
    (u = op874A i 5 ∧ v = op874B i 2) ∨
    (u = op874A i 4 ∧ v = op874B (i+1) 0) ∨
    (u = op874A i 3 ∧ v = op874B (i+1) 4)

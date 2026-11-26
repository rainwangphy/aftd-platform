import AFTD.Prelude
import AFTD.Kb.Tcs.Op874V

/-!
# op874bit

Topic: graphs   Node: c4e15900bdf1

Provenance: helper lemma. step towards op874_mixed_matching_overlap_gadget_chain

The matching-cut bit function, with the two prescribed local patterns on A and B vertices.
-/

/-- The bit labelling: [T,F,F,T,F,T,T,F] on A-vertices, [F,F,T,F,T,T,F,T] on B-vertices. -/
def op874bit {k : ℕ} (v : op874V k) : Bool := 
  match v with
  | ((_, false), j) => (![true,false,false,true,false,true,true,false] : Fin 8 → Bool) j
  | ((_, true), j) => (![false,false,true,false,true,true,false,true] : Fin 8 → Bool) j

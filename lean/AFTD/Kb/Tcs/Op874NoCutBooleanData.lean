import AFTD.Prelude

/-!
# op874_no_cut_boolean_data

Topic: graphs   Node: 99d4d1c8a016

Provenance: helper lemma. Finite verification associated with experiment 35469.

Boolean neighbor table and crossing-edge predicate for the twelve-vertex graph.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1081NoCut

def neighbors : Array (Array (Fin 12)) := #[
  #[2,8,11], #[7,8,10], #[0,5,7], #[6,7,9],
  #[5,6,8], #[2,4,9], #[3,4,10], #[1,2,3],
  #[0,1,4], #[3,5,11], #[1,6,11], #[0,9,10]]

def good (f : Fin 12 → Bool) : Bool :=
  (List.finRange 12).all fun v =>
    ((List.finRange 3).filter fun k => f v != f ((neighbors[v.val]!)[k.val]!)).length == 1

def assign (b0 b1 b2 b3 : Bool) (tail : Fin 8 → Bool) : Fin 12 → Bool :=
  Fin.cons b0 (Fin.cons b1 (Fin.cons b2 (Fin.cons b3 tail)))
end In1081NoCut

def op874_no_cut_boolean_data : Bool := true

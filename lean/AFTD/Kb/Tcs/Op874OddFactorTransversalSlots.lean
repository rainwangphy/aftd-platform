import AFTD.Prelude

/-!
# op874_odd_factor_transversal_slots

Topic: graphs   Node: c09ed32d79d9

Provenance: helper lemma. Explicit three odd-cycle independent-transversal obstruction based on https://arxiv.org/html/2309.12150 section 2.2; experiment 35359.

Seven triples of vertices in three disjoint seven-cycles, encoded as integers from zero to twenty.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1081Obstruction

def slots : Array (Array Nat) := #[
  #[0,2,5], #[7,9,12], #[14,16,19], #[1,11,13],
  #[4,18,20], #[3,8,10], #[6,15,17]]

def pick (code group : Nat) : Nat :=
  (slots[group]!)[(code / 3 ^ group) % 3]!

def conflict (x y : Nat) : Bool :=
  (x / 7 == y / 7) && (((x % 7 + 1) % 7 == y % 7) || ((y % 7 + 1) % 7 == x % 7))

def bad (code : Nat) : Bool :=
  (List.range 7).any fun i => (List.range 7).any fun j =>
    (i < j) && conflict (pick code i) (pick code j)

end In1081Obstruction

def op874_odd_factor_transversal_slots : Array (Array Nat) := In1081Obstruction.slots

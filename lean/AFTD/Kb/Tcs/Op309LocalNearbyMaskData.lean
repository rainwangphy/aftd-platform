import AFTD.Prelude
import AFTD.Kb.Tcs.Bit

/-!
# op309_local_nearby_mask_data

Topic: combinatorics   Node: 44245c421e76

Provenance: helper lemma. OP-309 local selection barrier, IN-1099; experiments 36441–36448.

Explicit edge table, neighborhood masks, domination, component and forbidden-pattern checks for a ten-vertex local exchange example.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace In1099Nearby

def edgeEnds : List (Nat × Nat) := [(0,4), (0,7), (0,9), (1,5), (1,6), (1,7), (2,5), (2,6), (2,8), (3,7), (3,8), (3,9), (4,8), (4,9), (5,6)]
def incident : List (List Nat) := [[0, 1, 2], [3, 4, 5], [6, 7, 8], [9, 10, 11], [0, 12, 13], [3, 6, 14], [4, 7, 14], [1, 5, 9], [8, 10, 12], [2, 11, 13]]
def adjacent : List (List Nat) := [[1, 2, 12, 13], [0, 2, 5, 9], [0, 1, 11, 13], [4, 5, 6, 14], [3, 5, 7, 14], [1, 3, 4, 9], [3, 7, 8, 14], [4, 6, 8, 14], [6, 7, 10, 12], [1, 5, 10, 11], [8, 9, 11, 12], [2, 9, 10, 13], [0, 8, 10, 13], [0, 2, 11, 12], [3, 4, 6, 7]]
def triangles : List Nat := [8197, 16408, 16576]
def connectedFour : List Nat := [39, 519, 2055, 4103, 8199, 43, 51, 547, 4131, 8227, 4355, 1539, 2563, 4611, 8707, 5123, 10243, 12291, 4357, 2565, 3077, 5125, 6149, 10245, 12293, 4417, 4481, 5377, 12545, 5633, 10753, 7169, 11265, 13313, 14337, 46, 54, 550, 2086, 8230, 1542, 2566, 8710, 3078, 10246, 12294, 58, 106, 554, 16426, 178, 562, 16434, 1570, 2594, 1794, 3586, 5634, 10754, 2596, 3332, 12548, 3588, 10756, 7172, 11268, 13316, 14340, 120, 184, 568, 16440, 216, 344, 16472, 408, 16536, 232, 360, 616, 16488, 16552, 1576, 2600, 16936, 456, 16584, 1352, 4424, 16712, 16776, 240, 16496, 432, 688, 16560, 1584, 2608, 16944, 464, 16592, 16720, 1424, 4496, 16784, 1824, 3616, 5664, 10784, 1472, 4544, 16832, 1856, 3392, 5440, 17728, 12608, 20800, 1920, 3456, 5504, 17792, 12672, 20864, 3840, 5888, 7424, 11520, 13568, 14592, 7680, 11776, 13824, 14848, 15360]
def badPatterns : List Nat := [24, 192, 1029, 8197, 2561, 8705, 3073, 518, 2054, 2562, 8706, 2564, 5124, 7168, 11264, 13312, 14336]
def exceptions : List Nat := [21602, 21666, 19554, 28770]
def base : Nat := 21602

def bit (r i : Nat) : Bool := r.testBit i
def subsetMask (r p : Nat) : Bool := Nat.land r p == p
def flip (r i : Nat) : Nat := Nat.xor r (2^i)
def nearby : List Nat :=
  [base] ++ (List.range 15).map (flip base) ++
  (List.range 15).flatMap (fun i => (List.range 15).filterMap fun j =>
    if i < j then some (flip (flip base i) j) else none) ++
  (List.range 15).flatMap (fun i => (List.range 15).flatMap fun j =>
    (List.range 15).filterMap fun k =>
      if i < j && j < k then some (flip (flip (flip base i) j) k) else none)

def dominates (r : Nat) : Bool :=
  (List.range 15).all fun i => (adjacent[i]!).any (bit r)

def degreeAt (r v : Nat) : Nat := ((incident[v]!).filter (bit r)).length

def middleCount (r : Nat) : Nat :=
  ((List.range 15).filter fun i =>
    let e := edgeEnds[i]!
    bit r i && degreeAt r e.1 == 2 && degreeAt r e.2 == 2).length

def eligible (r : Nat) : Bool :=
  dominates r && middleCount r ≤ 1 &&
  triangles.all (fun t => !(subsetMask r t)) &&
  connectedFour.all (fun t => !(subsetMask r t))

def check (r : Nat) : Bool :=
  if !(dominates r) || badPatterns.any (subsetMask r) then true
  else if !(eligible r) then true else exceptions.contains r


end In1099Nearby

def op309_local_nearby_mask_data : Nat := In1099Nearby.base

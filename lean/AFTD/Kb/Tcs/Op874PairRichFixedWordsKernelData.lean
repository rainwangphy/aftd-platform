import AFTD.Prelude
import AFTD.Kb.Tcs.Bit

/-!
# op874_pair_rich_fixed_words_kernel_data

Topic: graphs   Node: c88d94f302f2

Provenance: helper lemma. Fixed-high matching-factor obstruction, experiments 36048 and 36050.

The explicit two five-cycle words, matching permutation, low-bit and ownership encoding, high-port tables and Boolean interface checker for the fixed-word obstruction.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace In1098Bit

def perm (i : Fin 5) : Fin 5 := ![0,4,3,2,1] i
def word (s : Bool) (i : Fin 5) : Nat :=
  if s then (![2,0,3,1,3] : Fin 5 → Nat) i else (![3,2,3,2,1] : Fin 5 → Nat) i

def bit (mask : BitVec 5) (i : Fin 5) : Bool := mask.getLsbD i.val
def idx (s : Bool) (i : Fin 5) : Fin 5 := if s then perm i else i
def colorBit (b : BitVec 5) (s : Bool) (i : Fin 5) : Bool := bit b (idx s i)
def port (x y : BitVec 5) (s : Bool) (i : Fin 5) : Nat :=
  let j := idx s i
  if bit x j == s then 0 else if bit y j then 2 else 1

def phase (z : BitVec 10) (s : Bool) (i : Fin 5) : Bool :=
  z.getLsbD (if s then i.val + 5 else i.val)
def high (s : Bool) (i : Fin 5) (second : Bool) : BitVec 3 :=
  let first : Fin 5 → BitVec 3 := if s then ![2,3,3,2,2] else ![2,2,2,2,2]
  let last : Fin 5 → BitVec 3 := if s then ![3,5,4,4,4] else ![4,3,3,3,5]
  if second then last i else first i
def hidden (b x y : BitVec 5) (z : BitVec 10) (s : Bool) (i : Fin 5) (p : Nat) : BitVec 3 :=
  let matching := bit x (idx s i) == s
  let dir := bit y (idx s i)
  let selected := if p == 0 then matching else if p == 1 then !matching && !dir else !matching && dir
  let isSecond := if p == 0 then false else if p == 1 then !matching else true
  if selected then (if colorBit b s i then 0 else 1)
  else
    high s i (isSecond != phase z s i)

def disjoint2 (a b c d : BitVec 3) : Bool := a != c && a != d && b != c && b != d

def highok (b x y : BitVec 5) (z : BitVec 10) : Bool :=
  let h := hidden b x y z
  let fact := [false,true].all fun s => (List.finRange 5).all fun i =>
    disjoint2 (h s i 0) (h s i 1) (h s (i+1) 0) (h s (i+1) 2)
  let matching := (List.finRange 5).all fun i =>
    disjoint2 (h false i 1) (h false i 2) (h true (perm i) 1) (h true (perm i) 2)
  fact && matching

end In1098Bit

def op874_pair_rich_fixed_words_kernel_data (b x y : BitVec 5) (z : BitVec 10) : Bool := In1098Bit.highok b x y z

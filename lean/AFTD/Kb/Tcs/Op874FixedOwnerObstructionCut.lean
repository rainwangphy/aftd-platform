import AFTD.Prelude

/-!
# op874_fixed_owner_obstruction_cut

Topic: graphs   Node: f6941ac0afe3

Provenance: helper lemma. Finite matching-cut calculation for the fixed-owner obstruction to OP-874; experiments 43171–43177.

For the fixed fourteen-vertex obstruction data, the displayed matching-constant cut has value 12, every matching-constant cut has value at most 12, and the displayed bits are mixed on each of the two displayed factor cycles.
-/

namespace IN1258Cut

def L : Fin 21 → Fin 14 := ![0,0,0,1,1,1,2,2,2,3,3,4,4,5,5,6,6,7,8,9,11]
def R : Fin 21 → Fin 14 := ![3,7,10,4,5,8,7,9,10,10,13,8,11,6,12,9,13,11,12,12,13]
def in1258_match : Finset (Fin 21) := {2,3,7,10,13,17,18}
def owner : Fin 14 → Fin 7 := ![4,5,2,3,5,1,1,0,6,2,4,0,6,3]
def C5 : Finset (Fin 14) := {0,2,3,7,10}
def C9 : Finset (Fin 14) := {1,4,5,6,8,9,11,12,13}
def witness : Fin 7 → Bool := ![false,false,true,true,false,true,false]
def score (x : Fin 7 → Bool) : Nat :=
  ((Finset.univ : Finset (Fin 21)).filter fun e => e ∉ in1258_match ∧ x (owner (L e)) ≠ x (owner (R e))).card

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem score_bound : ∀ x : Fin 7 → Bool, score x ≤ 12 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem score_witness : score witness = 12 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem factor_mixed :
  (∃ u ∈ C5, ∃ v ∈ C5, witness (owner u) ≠ witness (owner v)) ∧
  (∃ u ∈ C9, ∃ v ∈ C9, witness (owner u) ≠ witness (owner v)) := by decide

end IN1258Cut

theorem op874_fixed_owner_obstruction_cut :
  let L : Fin 21 → Fin 14 := ![0,0,0,1,1,1,2,2,2,3,3,4,4,5,5,6,6,7,8,9,11]
  let R : Fin 21 → Fin 14 := ![3,7,10,4,5,8,7,9,10,10,13,8,11,6,12,9,13,11,12,12,13]
  let in1258_match : Finset (Fin 21) := {2,3,7,10,13,17,18}
  let owner : Fin 14 → Fin 7 := ![4,5,2,3,5,1,1,0,6,2,4,0,6,3]
  let C5 : Finset (Fin 14) := {0,2,3,7,10}
  let C9 : Finset (Fin 14) := {1,4,5,6,8,9,11,12,13}
  let witness : Fin 7 → Bool := ![false,false,true,true,false,true,false]
  let score (x : Fin 7 → Bool) : Nat :=
    ((Finset.univ : Finset (Fin 21)).filter fun e => e ∉ in1258_match ∧ x (owner (L e)) ≠ x (owner (R e))).card

  (∀ x : Fin 7 → Bool, score x ≤ 12) ∧ score witness = 12 ∧
  (∃ u ∈ C5, ∃ v ∈ C5, witness (owner u) ≠ witness (owner v)) ∧
  (∃ u ∈ C9, ∃ v ∈ C9, witness (owner u) ≠ witness (owner v)) := by
  dsimp only
  exact ⟨IN1258Cut.score_bound, IN1258Cut.score_witness,
    IN1258Cut.factor_mixed.1, IN1258Cut.factor_mixed.2⟩

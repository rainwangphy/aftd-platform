import AFTD.Prelude

/-!
# op874_fixed_owner_obstruction_factor_cycles

Topic: graphs   Node: 9ffe6271b38e

Provenance: helper lemma. Factor-cycle certificate for the fixed-owner obstruction to OP-874; experiment 43175.

The factor of the explicit graph and matching in the fixed-owner obstruction is precisely the two displayed cycles of lengths five and nine, whose vertex sets are those used in the mixed-cut calculation.
-/

namespace IN1258FactorCycles
def in1258_left : Fin 21 → Fin 14 := ![0,0,0,1,1,1,2,2,2,3,3,4,4,5,5,6,6,7,8,9,11]
def in1258_right : Fin 21 → Fin 14 := ![3,7,10,4,5,8,7,9,10,10,13,8,11,6,12,9,13,11,12,12,13]
def in1258_match : Finset (Fin 21) := {2,3,7,10,13,17,18}

def in1258_cycle5 : Fin 5 → Fin 14 := ![2,7,0,3,10]
def in1258_cycle9 : Fin 9 → Fin 14 := ![6,9,12,5,1,8,4,11,13]
def in1258_C5 : Finset (Fin 14) := {0,2,3,7,10}
def in1258_C9 : Finset (Fin 14) := {1,4,5,6,8,9,11,12,13}
def in1258_ends (e : Fin 21) : Sym2 (Fin 14) := s(in1258_left e,in1258_right e)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem factor_cycles :
    ((Finset.univ : Finset (Fin 5)).image in1258_cycle5 = in1258_C5) ∧
    ((Finset.univ : Finset (Fin 9)).image in1258_cycle9 = in1258_C9) ∧
    (∀ i : Fin 5, ∃ e : Fin 21, e ∉ in1258_match ∧ in1258_ends e = s(in1258_cycle5 i, in1258_cycle5 (i+1))) ∧
    (∀ i : Fin 9, ∃ e : Fin 21, e ∉ in1258_match ∧ in1258_ends e = s(in1258_cycle9 i, in1258_cycle9 (i+1))) ∧
    (∀ e : Fin 21, e ∉ in1258_match →
      (∃ i : Fin 5, in1258_ends e = s(in1258_cycle5 i, in1258_cycle5 (i+1))) ∨
      (∃ i : Fin 9, in1258_ends e = s(in1258_cycle9 i, in1258_cycle9 (i+1)))) := by decide

end IN1258FactorCycles

theorem op874_fixed_owner_obstruction_factor_cycles :
  let in1258_left : Fin 21 → Fin 14 := ![0,0,0,1,1,1,2,2,2,3,3,4,4,5,5,6,6,7,8,9,11]
  let in1258_right : Fin 21 → Fin 14 := ![3,7,10,4,5,8,7,9,10,10,13,8,11,6,12,9,13,11,12,12,13]
  let in1258_match : Finset (Fin 21) := {2,3,7,10,13,17,18}

  let in1258_cycle5 : Fin 5 → Fin 14 := ![2,7,0,3,10]
  let in1258_cycle9 : Fin 9 → Fin 14 := ![6,9,12,5,1,8,4,11,13]
  let in1258_C5 : Finset (Fin 14) := {0,2,3,7,10}
  let in1258_C9 : Finset (Fin 14) := {1,4,5,6,8,9,11,12,13}
  let in1258_ends (e : Fin 21) : Sym2 (Fin 14) := s(in1258_left e,in1258_right e)
  ((Finset.univ : Finset (Fin 5)).image in1258_cycle5 = in1258_C5) ∧
  ((Finset.univ : Finset (Fin 9)).image in1258_cycle9 = in1258_C9) ∧
  (∀ i : Fin 5, ∃ e : Fin 21, e ∉ in1258_match ∧ in1258_ends e = s(in1258_cycle5 i, in1258_cycle5 (i+1))) ∧
  (∀ i : Fin 9, ∃ e : Fin 21, e ∉ in1258_match ∧ in1258_ends e = s(in1258_cycle9 i, in1258_cycle9 (i+1))) ∧
  (∀ e : Fin 21, e ∉ in1258_match →
    (∃ i : Fin 5, in1258_ends e = s(in1258_cycle5 i, in1258_cycle5 (i+1))) ∨
    (∃ i : Fin 9, in1258_ends e = s(in1258_cycle9 i, in1258_cycle9 (i+1)))) := by
  dsimp only
  exact IN1258FactorCycles.factor_cycles

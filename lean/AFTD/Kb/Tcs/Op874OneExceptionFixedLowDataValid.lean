import AFTD.Prelude

/-!
# op874_one_exception_fixed_low_data_valid

Topic: graphs   Node: 51569ae5d0d6

Provenance: helper lemma. Ten-vertex fixed-low obstruction, experiments 36262 and 36267.

The fixed ten-vertex factor, matching, matching bits and selected low ports satisfy matching consistency, exactly one owner on each matching edge, same-bit factor-edge coverage, no double factor ownership, and exactly one exception to the displayed per-cycle directions.
-/

theorem op874_one_exception_fixed_low_data_valid :
  let prev : Fin 10 → Fin 10 := ![2,0,1,9,3,4,5,6,7,8]
  let next : Fin 10 → Fin 10 := ![1,2,0,4,5,6,7,8,9,3]
  let mate : Fin 10 → Fin 10 := ![7,5,6,8,9,1,2,0,3,4]
  let bit : Fin 10 → Bool := ![true,true,false,false,true,true,false,true,false,true]
  let owner : Fin 10 → Fin 10 := ![1,5,1,4,5,6,2,0,3,4]
  (∀ i, mate (mate i) = i ∧ mate i ≠ i ∧ bit (mate i) = bit i ∧ prev (next i) = i ∧ next (prev i) = i) ∧
  (∀ i, owner i = mate i ∨ owner i = prev i ∨ owner i = next i) ∧
  (∀ i, owner i = mate i ↔ owner (mate i) ≠ i) ∧
  (∀ i, bit i = bit (next i) → owner i = next i ∨ owner (next i) = i) ∧
  (∀ i, ¬ (owner i = next i ∧ owner (next i) = i)) ∧
  (∀ i, owner i ≠ mate i → (i = 0 ∧ owner i = next i) ∨ (i ≠ 0 ∧ (if i.val < 3 then owner i = prev i else owner i = next i))) := by decide

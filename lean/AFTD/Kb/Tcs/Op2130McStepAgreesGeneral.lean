import AFTD.Prelude
import AFTD.Kb.Tcs.Op2130IntervalMarginalRecursiveCounterexample
import AFTD.Kb.Tcs.CarpoolStep

/-!
# op2130_mc_step_agrees_general

Topic: online_algorithms   Node: fd249d4610ac

Provenance: helper lemma. OP-2130, list-state and finite-path greedy update

For any list of n discrepancies and any valid path edge j,j+1, the list-state greedy update agrees coordinatewise with the existing finite-vertex carpool step.
-/

set_option maxHeartbeats 2000000

theorem op2130_mc_step_agrees_general (n : ℕ) (d : List ℤ) (hd : d.length = n) (j : ℕ) (hj : j+1 < n) (c : Bool) (v : Fin n) :
 let D : Fin n → ℤ := fun i => d.getD i.val 0
 let a : Fin n := ⟨j, by omega⟩
 let b : Fin n := ⟨j+1, hj⟩
 (op2130_mc_step d j c).getD v.val 0 =
   carpool_step n D (a,b) (if D a < D b then true else if D b < D a then false else c) v := by
  have h0 : j < d.length := by omega
  have h1 : j+1 < d.length := by omega
  by_cases hv0 : v.val = j
  · have hv1 : v.val ≠ j+1 := by omega
    simp [op2130_mc_step, carpool_step, List.getD_eq_getElem?_getD,
      List.getElem?_set, Fin.ext_iff, hv0, hv1, h0, h1] <;> split_ifs <;> simp_all <;> omega
  · by_cases hv1 : v.val = j+1
    · simp [op2130_mc_step, carpool_step, List.getD_eq_getElem?_getD,
        List.getElem?_set, Fin.ext_iff, hv0, hv1, h0, h1] <;> split_ifs <;> simp_all <;> omega
    · simp [op2130_mc_step, carpool_step, List.getD_eq_getElem?_getD,
        List.getElem?_set, Fin.ext_iff, hv0, hv1, Ne.symm hv0, Ne.symm hv1, h0, h1]

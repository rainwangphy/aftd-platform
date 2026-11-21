import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolStep

/-!
# op_2130_centered_path_potential_right_step

Topic: online_algorithms   Node: d86052a4aa73

Provenance: helper lemma. OP-2130: exact increment of the centered weighted path potential

Moving one unit from vertex i to its right neighbor increases the centered weighted path potential by two.
-/

theorem op_2130_centered_path_potential_right_step (D : ℕ) (hD : 1 ≤ D) (d : Fin (2 * D) → ℤ) (i : Fin (2 * D - 1)) : (∑ v : Fin (2 * D), (2 * (v.val : ℤ) + 1 - 2 * (D : ℤ)) * carpool_step (2 * D) d (⟨i.val, by omega⟩, ⟨i.val + 1, by omega⟩) false v) = (∑ v : Fin (2 * D), (2 * (v.val : ℤ) + 1 - 2 * (D : ℤ)) * d v) + 2 := by
  simp [carpool_step, mul_add, mul_ite, Finset.sum_add_distrib] <;> ring

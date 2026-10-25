import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryAffineLiftFourthDifference

/-!
# parity_phase_fourth_difference

Topic: quantum   Node: 4a78f4704e92

Provenance: helper lemma. Supporting algebra for OP-3, arXiv:2610.01024, Section E.1; developed in deep session IN-184. These helpers do not establish a lower bound for arbitrary circuit gate lists.

Every finite Z/8 linear combination of lifted binary linear forms has zero fourth alternating difference on each four-direction cube.
-/

theorem parity_phase_fourth_difference {V ι : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [Fintype ι]
    (c : ι → ZMod 8) (L : ι → V →ₗ[ZMod 2] ZMod 2)
    (u : Fin 4 → V) :
    (∑ x : Fin 4 → ZMod 2,
      (-1 : ZMod 8) ^ (∑ i : Fin 4, (x i).val) *
        (∑ j : ι, c j * ((L j (∑ i : Fin 4, x i • u i)).val : ZMod 8))) = 0 := by
  classical
  simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j hj
  have hf := binary_affine_lift_fourth_difference 0
    (fun i : Fin 4 => L j (u i))
  simp only [zero_add] at hf
  calc
    (∑ x : Fin 4 → ZMod 2,
      (-1 : ZMod 8) ^ (∑ i : Fin 4, (x i).val) *
        (c j * (((∑ i : Fin 4, x i * L j (u i)).val : ℕ) : ZMod 8))) =
      c j * (∑ x : Fin 4 → ZMod 2,
        (-1 : ZMod 8) ^ (∑ i : Fin 4, (x i).val) *
          (((∑ i : Fin 4, L j (u i) * x i).val : ℕ) : ZMod 8)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        simp only [mul_comm]
        ring
    _ = 0 := by rw [hf, mul_zero]

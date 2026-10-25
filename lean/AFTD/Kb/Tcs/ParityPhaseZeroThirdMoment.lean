import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryLinearLiftThirdDifference

/-!
# parity_phase_zero_third_moment

Topic: quantum   Node: f57689c8e68d

Provenance: helper lemma. Phase-to-moment bridge for OP-3, arXiv:2610.01024, Fact 21 and Section E.1; this states the necessary zero-phase moment identity in a binary linear-space formulation.

If a finite parity-phase polynomial is identically zero modulo eight, its binary third-moment tensor is zero; allowing repeated directions also covers moments of orders one and two.
-/

abbrev parity_phase_zero_third_moment_rho : ZMod 8 →+* ZMod 2 :=
  ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2)

lemma parity_phase_zero_third_moment_rho_val (r : ZMod 2) :
    parity_phase_zero_third_moment_rho (((r.val : ℕ) : ZMod 8)) = r := by
  revert r
  decide

lemma parity_phase_zero_third_moment_rho_of_four_mul_zero (t : ZMod 8) (h : 4 * t = 0) :
    parity_phase_zero_third_moment_rho t = 0 := by
  revert t
  decide

lemma parity_phase_zero_third_moment_l_eval {V ι : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (L : ι → V →ₗ[ZMod 2] ZMod 2) (v w z : V) (j : ι) (x : Fin 3 → ZMod 2) :
    ∑ i : Fin 3, (![L j v, L j w, L j z] i : ZMod 2) * x i = L j (x 0 • v + x 1 • w + x 2 • z) := by
  rw [Fin.sum_univ_three]
  change L j v * x 0 + L j w * x 1 + L j z * x 2 = _
  rw [map_add, map_add, map_smul, map_smul, map_smul]
  ring

lemma parity_phase_zero_third_moment_double_sum_zero {V ι : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype ι]
    (c : ι → ZMod 8) (L : ι → V →ₗ[ZMod 2] ZMod 2)
    (hzero : ∀ v, (∑ j : ι, c j * ((L j v).val : ZMod 8)) = 0) (v w z : V) :
    (∑ j : ι, c j * (∑ x : Fin 3 → ZMod 2,
      (-1 : ZMod 8) ^ (∑ i : Fin 3, (x i).val) *
        (((L j (x 0 • v + x 1 • w + x 2 • z)).val : ℕ) : ZMod 8))) = 0 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h_inner : ∀ x : Fin 3 → ZMod 2,
      (∑ j : ι, c j * ((-1 : ZMod 8) ^ (∑ i : Fin 3, (x i).val) *
        (((L j (x 0 • v + x 1 • w + x 2 • z)).val : ℕ) : ZMod 8))) = 0 := by
    intro x
    have h_term : ∀ j : ι, c j * ((-1 : ZMod 8) ^ (∑ i : Fin 3, (x i).val) *
        (((L j (x 0 • v + x 1 • w + x 2 • z)).val : ℕ) : ZMod 8)) =
        (-1 : ZMod 8) ^ (∑ i : Fin 3, (x i).val) * (c j * (((L j (x 0 • v + x 1 • w + x 2 • z)).val : ℕ) : ZMod 8)) := by
      intro j
      ring
    simp_rw [h_term, ← Finset.mul_sum]
    rw [hzero]
    ring
  simp_rw [h_inner]
  simp

lemma parity_phase_zero_third_moment_four_mul_sum_zero {V ι : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype ι]
    (c : ι → ZMod 8) (L : ι → V →ₗ[ZMod 2] ZMod 2)
    (hzero : ∀ v, (∑ j : ι, c j * ((L j v).val : ZMod 8)) = 0) (v w z : V) :
    4 * (∑ j : ι, c j * (((L j v * L j w * L j z).val : ℕ) : ZMod 8)) = 0 := by
  have h := parity_phase_zero_third_moment_double_sum_zero c L hzero v w z
  have h_diff : ∀ j : ι, (∑ x : Fin 3 → ZMod 2,
      (-1 : ZMod 8) ^ (∑ i : Fin 3, (x i).val) *
        (((L j (x 0 • v + x 1 • w + x 2 • z)).val : ℕ) : ZMod 8)) =
      4 * (((L j v * L j w * L j z).val : ℕ) : ZMod 8) := by
    intro j
    have hd := binary_linear_lift_third_difference (![L j v, L j w, L j z])
    simp_rw [parity_phase_zero_third_moment_l_eval] at hd
    have h_prod : (![L j v, L j w, L j z] 0 * ![L j v, L j w, L j z] 1 * ![L j v, L j w, L j z] 2) =
        L j v * L j w * L j z := rfl
    rw [h_prod] at hd
    exact hd
  simp_rw [h_diff] at h
  have h_factor : (∑ j : ι, c j * (4 * (((L j v * L j w * L j z).val : ℕ) : ZMod 8))) =
      4 * (∑ j : ι, c j * (((L j v * L j w * L j z).val : ℕ) : ZMod 8)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h_factor] at h
  exact h

theorem parity_phase_zero_third_moment {V ι : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Fintype ι] (c : ι → ZMod 8) (L : ι → V →ₗ[ZMod 2] ZMod 2) (hzero : ∀ v, (∑ j : ι, c j * ((L j v).val : ZMod 8)) = 0) : ∀ v w z : V, (∑ j : ι, ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2) (c j) * L j v * L j w * L j z) = 0 := by
  intro v w z
  have h4 := parity_phase_zero_third_moment_four_mul_sum_zero c L hzero v w z
  have hrho := parity_phase_zero_third_moment_rho_of_four_mul_zero _ h4
  rw [map_sum] at hrho
  have h_term : ∀ j : ι, parity_phase_zero_third_moment_rho (c j * (((L j v * L j w * L j z).val : ℕ) : ZMod 8)) =
      ZMod.castHom (by decide : 2 ∣ 8) (ZMod 2) (c j) * L j v * L j w * L j z := by
    intro j
    rw [map_mul]
    rw [parity_phase_zero_third_moment_rho_val]
    ring
  simp_rw [h_term] at hrho
  exact hrho

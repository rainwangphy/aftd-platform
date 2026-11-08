import AFTD.Prelude
import AFTD.Kb.Tcs.AmpDampingGenerator
import AFTD.Kb.Tcs.SpectralMinRe
import AFTD.Kb.Tcs.PAmpDamping
import AFTD.Kb.Tcs.VAmpDamping

/-!
# amp_damping_shift_spectral_min_re

Topic: quantum   Node: e246b4468b66

Provenance: formalization of a published result. Source: arXiv:2610.37187 Proposition 9 (eq. 7.1), m(L_c) = c - 1

The smallest real part of an eigenvalue of $L_c = G + c\,\mathrm{id}$ is $c - 1$.
-/

theorem amp_damping_spmin_apply_entry (d : ℕ) (h : 2 ≤ d) (c : ℝ) (X : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    ((amp_damping_generator d h + (c : ℂ) • LinearMap.id :
      Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) X) i j =
      (if i = ⟨0, by omega⟩ ∧ j = ⟨0, by omega⟩ then X ⟨1, by omega⟩ ⟨1, by omega⟩ else 0)
      - (1/2 : ℂ) * ((if i = ⟨1, by omega⟩ then X i j else 0) + (if j = ⟨1, by omega⟩ then X i j else 0))
      + c * X i j := by
  simp only [amp_damping_generator, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply, LinearMap.id_apply,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  simp [v_amp_damping, p_amp_damping, Matrix.mul_apply, Matrix.star_apply, ite_and,
    Finset.sum_ite_eq']
  simp only [apply_ite (starRingEnd ℂ), map_one, map_zero, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  by_cases hi : i = ⟨1, by omega⟩ <;> by_cases hj : j = ⟨1, by omega⟩ <;> simp [hi, hj]

theorem amp_damping_spmin_mem_spectrum_cases (d : ℕ) (h : 2 ≤ d) (c : ℝ) (μ : ℂ)
    (hμ : μ ∈ spectrum ℂ (amp_damping_generator d h + (c : ℂ) • LinearMap.id :
      Module.End ℂ (Matrix (Fin d) (Fin d) ℂ))) :
    μ = c ∨ μ = c - 1/2 ∨ μ = c - 1 := by
  rw [← Module.End.hasEigenvalue_iff_mem_spectrum] at hμ
  obtain ⟨X, hX⟩ := hμ.exists_hasEigenvector
  by_contra hne
  push Not at hne
  obtain ⟨h1, h2, h3⟩ := hne
  apply hX.2
  have eq : ∀ i j, μ * X i j = (if i = ⟨0, by omega⟩ ∧ j = ⟨0, by omega⟩ then X ⟨1, by omega⟩ ⟨1, by omega⟩ else 0)
      - (1/2 : ℂ) * ((if i = ⟨1, by omega⟩ then X i j else 0) + (if j = ⟨1, by omega⟩ then X i j else 0))
      + c * X i j := by
    intro i j
    rw [← amp_damping_spmin_apply_entry d h c X i j, hX.apply_eq_smul]
    simp
  have h01 : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hx11 : X ⟨1, by omega⟩ ⟨1, by omega⟩ = 0 := by
    have e := eq ⟨1, by omega⟩ ⟨1, by omega⟩
    simp only [h01.symm, false_and, if_false, if_true] at e
    have : (μ - (c - 1)) * X ⟨1, by omega⟩ ⟨1, by omega⟩ = 0 := by linear_combination e
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd (sub_eq_zero.mp h') h3
    · exact h'
  ext i j
  have e := eq i j
  by_cases hi : i = ⟨1, by omega⟩ <;> by_cases hj : j = ⟨1, by omega⟩
  · subst hi; subst hj; simpa using hx11
  · subst hi
    simp only [h01.symm, false_and, hj, if_false, if_true] at e
    have : (μ - (c - 1/2)) * X ⟨1, by omega⟩ j = 0 := by linear_combination e
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd (sub_eq_zero.mp h') h2
    · simpa using h'
  · subst hj
    simp only [h01.symm, and_false, hi, if_false, if_true] at e
    have : (μ - (c - 1/2)) * X i ⟨1, by omega⟩ = 0 := by linear_combination e
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd (sub_eq_zero.mp h') h2
    · simpa using h'
  · simp only [hi, hj, if_false] at e
    have : (μ - c) * X i j = (if i = ⟨0, by omega⟩ ∧ j = ⟨0, by omega⟩ then X ⟨1, by omega⟩ ⟨1, by omega⟩ else 0) := by
      linear_combination e
    rw [hx11, ite_self] at this
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd (sub_eq_zero.mp h') h1
    · simpa using h'

theorem amp_damping_spmin_mem_c_sub_one (d : ℕ) (h : 2 ≤ d) (c : ℝ) :
    ((c : ℂ) - 1) ∈ spectrum ℂ (amp_damping_generator d h + (c : ℂ) • LinearMap.id :
      Module.End ℂ (Matrix (Fin d) (Fin d) ℂ)) := by
  rw [← Module.End.hasEigenvalue_iff_mem_spectrum]
  apply Module.End.hasEigenvalue_of_hasEigenvector
    (x := Matrix.single ⟨1, by omega⟩ ⟨1, by omega⟩ 1 - Matrix.single ⟨0, by omega⟩ ⟨0, by omega⟩ 1)
  have h01 : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  refine ⟨?_, ?_⟩
  · rw [Module.End.mem_eigenspace_iff]
    ext i j
    rw [amp_damping_spmin_apply_entry]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
    have hc : ∀ x : Fin d, x = ⟨0, by omega⟩ ∨ x = ⟨1, by omega⟩ ∨
        (x ≠ ⟨0, by omega⟩ ∧ x ≠ ⟨1, by omega⟩) := fun x => by tauto
    rcases hc i with rfl | rfl | ⟨hi0, hi1⟩ <;> rcases hc j with rfl | rfl | ⟨hj0, hj1⟩ <;>
      (try have hi0' := Ne.symm hi0) <;> (try have hi1' := Ne.symm hi1) <;>
      (try have hj0' := Ne.symm hj0) <;> (try have hj1' := Ne.symm hj1) <;>
      simp [h01, h01.symm, *] <;> ring
  · intro h0
    have := congrFun (congrFun h0 ⟨1, by omega⟩) ⟨1, by omega⟩
    simp [Matrix.single_apply, h01.symm] at this

theorem amp_damping_shift_spectral_min_re (d : ℕ) (h : 2 ≤ d) (c : ℝ) :
    spectral_min_re d (amp_damping_generator d h + (c : ℂ) • LinearMap.id) = c - 1 := by
  unfold spectral_min_re
  apply IsLeast.csInf_eq
  refine ⟨⟨(c : ℂ) - 1, amp_damping_spmin_mem_c_sub_one d h c, by simp⟩, ?_⟩
  rintro x ⟨μ, hμ, rfl⟩
  rcases amp_damping_spmin_mem_spectrum_cases d h c μ hμ with rfl | rfl | rfl <;> norm_num <;> linarith

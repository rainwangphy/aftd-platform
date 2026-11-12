import AFTD.Prelude
import AFTD.Tactic.NumBounds
import AFTD.Kb.Tcs.PptQutritSteeredEffect
import AFTD.Kb.Tcs.PptQutritSteeredNormalizer
import AFTD.Kb.Tcs.PptQutritSteeredUnnormalizedEffect
import AFTD.Kb.Tcs.PptQutritBellState
import AFTD.Kb.Tcs.PptQutritBellSetting
import AFTD.Kb.Tcs.PptQutritBellVector

/-!
# ppt_qutrit_steered_effect_incompatible

Topic: quantum   Node: 22b0dcb6e5f0

Provenance: helper lemma. Helper for OP-693; Bell inequality and explicit violation in arXiv:1405.4502 equations (4)–(8); steering-to-compatibility relation in arXiv:2010.04048 Appendix A.

The three normalized steered binary effects from the explicit PPT Bell example are not jointly measurable.
-/

open Matrix
open scoped ComplexOrder Matrix BigOperators
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
open scoped MatrixOrder
private lemma in767_originalproof_trace_psd {n : Type} [Fintype n] [DecidableEq n] {P ρ : Matrix n n ℂ}
    (hP : P.PosSemidef) (hρ : ρ.PosSemidef) : 0 ≤ (P * ρ).trace.re := by
  obtain ⟨X, hX, -, rfl⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hP.isHermitian
    (QuasispectrumRestricts.nnreal_of_nonneg hP.nonneg)
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← Matrix.mul_assoc]
  have h := hρ.mul_mul_conjTranspose_same X
  rw [← Matrix.star_eq_conjTranspose, hX.star_eq] at h
  exact (Complex.nonneg_iff.1 h.trace_nonneg).1

private noncomputable def in767_originalproof_dual_vec (i : Fin 4) : Fin 3 → ℂ :=
  if i = 0 then ![10599/1557500, 1791231/3115000, 1991/89000]
  else if i = 1 then ![-773727/1557500, -448691/1557500, 3993/178000]
  else if i = 2 then ![1565119/3115000, -455757/1557500, 1947/89000]
  else ![0, 0, 77/2000]

private lemma in767_originalproof_dual_vec0 : in767_originalproof_dual_vec 0 = ![10599/1557500, 1791231/3115000, 1991/89000] := by norm_num [in767_originalproof_dual_vec]
private lemma in767_originalproof_dual_vec1 : in767_originalproof_dual_vec 1 = ![-773727/1557500, -448691/1557500, 3993/178000] := by norm_num [in767_originalproof_dual_vec]
private lemma in767_originalproof_dual_vec2 : in767_originalproof_dual_vec 2 = ![1565119/3115000, -455757/1557500, 1947/89000] := by simp only [in767_originalproof_dual_vec, show (2 : Fin 4) ≠ 0 from by decide, show (2 : Fin 4) ≠ 1 from by decide, if_false, if_true]
private lemma in767_originalproof_dual_vec3 : in767_originalproof_dual_vec 3 = ![0, 0, 77/2000] := by simp only [in767_originalproof_dual_vec, show (3 : Fin 4) ≠ 0 from by decide, show (3 : Fin 4) ≠ 1 from by decide, show (3 : Fin 4) ≠ 2 from by decide, if_false]

private noncomputable def in767_originalproof_dual_p (i : Fin 4) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.vecMulVec (in767_originalproof_dual_vec i) (star (in767_originalproof_dual_vec i))

private noncomputable def in767_originalproof_dual_z (s : Fin 3 → Bool) : Matrix (Fin 3) (Fin 3) ℂ :=
  (2 : ℝ) • in767_originalproof_dual_p 3 + (if s 0 then in767_originalproof_dual_p 1 - in767_originalproof_dual_p 3 else 0) +
  (if s 1 then in767_originalproof_dual_p 0 - in767_originalproof_dual_p 3 else 0) +
  (if s 2 then in767_originalproof_dual_p 2 - in767_originalproof_dual_p 3 else 0)

private lemma in767_originalproof_dual_p_psd (i : Fin 4) : (in767_originalproof_dual_p i).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star _

private lemma in767_originalproof_dual_all_psd (s : Fin 3 → Bool) : (in767_originalproof_dual_z s).PosSemidef := by
  cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2
  · have he : in767_originalproof_dual_z s = in767_originalproof_dual_p 3 + in767_originalproof_dual_p 3 := by simp [in767_originalproof_dual_z, h0, h1, h2, two_smul] <;> abel
    rw [he]; exact (in767_originalproof_dual_p_psd 3).add (in767_originalproof_dual_p_psd 3)
  · have he : in767_originalproof_dual_z s = in767_originalproof_dual_p 2 + in767_originalproof_dual_p 3 := by simp [in767_originalproof_dual_z, h0, h1, h2, two_smul] <;> abel
    rw [he]; exact (in767_originalproof_dual_p_psd 2).add (in767_originalproof_dual_p_psd 3)
  · have he : in767_originalproof_dual_z s = in767_originalproof_dual_p 0 + in767_originalproof_dual_p 3 := by simp [in767_originalproof_dual_z, h0, h1, h2, two_smul] <;> abel
    rw [he]; exact (in767_originalproof_dual_p_psd 0).add (in767_originalproof_dual_p_psd 3)
  · have he : in767_originalproof_dual_z s = in767_originalproof_dual_p 0 + in767_originalproof_dual_p 2 := by simp [in767_originalproof_dual_z, h0, h1, h2, two_smul] <;> abel
    rw [he]; exact (in767_originalproof_dual_p_psd 0).add (in767_originalproof_dual_p_psd 2)
  · have he : in767_originalproof_dual_z s = in767_originalproof_dual_p 1 + in767_originalproof_dual_p 3 := by simp [in767_originalproof_dual_z, h0, h1, h2, two_smul] <;> abel
    rw [he]; exact (in767_originalproof_dual_p_psd 1).add (in767_originalproof_dual_p_psd 3)
  · have he : in767_originalproof_dual_z s = in767_originalproof_dual_p 1 + in767_originalproof_dual_p 2 := by simp [in767_originalproof_dual_z, h0, h1, h2, two_smul] <;> abel
    rw [he]; exact (in767_originalproof_dual_p_psd 1).add (in767_originalproof_dual_p_psd 2)
  · have he : in767_originalproof_dual_z s = in767_originalproof_dual_p 0 + in767_originalproof_dual_p 1 := by simp [in767_originalproof_dual_z, h0, h1, h2, two_smul] <;> abel
    rw [he]; exact (in767_originalproof_dual_p_psd 0).add (in767_originalproof_dual_p_psd 1)
  · let v : Fin 3 → ℂ := ![3533/5000, 0, 0]
    let w : Fin 3 → ℂ := ![0, 3533/5000, 0]
    have he : in767_originalproof_dual_z s = Matrix.vecMulVec v (star v) + Matrix.vecMulVec w (star w) := by
      simp only [in767_originalproof_dual_z, h0, h1, h2, if_true, in767_originalproof_dual_p,
        in767_originalproof_dual_vec0, in767_originalproof_dual_vec1, in767_originalproof_dual_vec2, in767_originalproof_dual_vec3, two_smul]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.vecMulVec_apply, Pi.star_apply] <;>
        norm_num [v, w, map_div₀, map_ofNat]
    rw [he]
    exact (Matrix.posSemidef_vecMulVec_self_star v).add (Matrix.posSemidef_vecMulVec_self_star w)

private lemma in767_originalproof_trace_matrix_sum (A : Matrix (Fin 3) (Fin 3) ℂ)
    (G : (Fin 3 → Bool) → Matrix (Fin 3) (Fin 3) ℂ) :
    (A * ∑ s, G s).trace.re = ∑ s, (A * G s).trace.re := by
  simp only [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]

private theorem in767_originalproof_any_not_joint (M : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ)
    (hcert : 2 * (in767_originalproof_dual_p 3).trace.re +
      ((in767_originalproof_dual_p 1 - in767_originalproof_dual_p 3) * M 0).trace.re +
      ((in767_originalproof_dual_p 0 - in767_originalproof_dual_p 3) * M 1).trace.re +
      ((in767_originalproof_dual_p 2 - in767_originalproof_dual_p 3) * M 2).trace.re < 0) :
    ¬ ∃ G : (Fin 3 → Bool) → Matrix (Fin 3) (Fin 3) ℂ,
      (∀ s, (G s).PosSemidef) ∧ (∑ s, G s = 1) ∧
      ∀ j : Fin 3, (∑ s, if s j then G s else 0) = M j := by
  classical
  rintro ⟨G, hG, hsum, hmarg⟩
  have hmargin (A : Matrix (Fin 3) (Fin 3) ℂ) (j : Fin 3) :
      (∑ s, if s j then (A * G s).trace.re else 0) = (A * M j).trace.re := by
    rw [← hmarg j, in767_originalproof_trace_matrix_sum]
    apply Finset.sum_congr rfl
    intro s _
    split_ifs <;> simp_all
  have hsplit (s : Fin 3 → Bool) :
      (in767_originalproof_dual_z s * G s).trace.re =
        2 * (in767_originalproof_dual_p 3 * G s).trace.re +
        (if s 0 then ((in767_originalproof_dual_p 1 - in767_originalproof_dual_p 3) * G s).trace.re else 0) +
        (if s 1 then ((in767_originalproof_dual_p 0 - in767_originalproof_dual_p 3) * G s).trace.re else 0) +
        (if s 2 then ((in767_originalproof_dual_p 2 - in767_originalproof_dual_p 3) * G s).trace.re else 0) := by
    cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;>
      simp [in767_originalproof_dual_z, h0, h1, h2, two_smul, Matrix.add_mul, Matrix.sub_mul, Matrix.trace_add, Matrix.trace_sub] <;> ring
  have heq : (∑ s, (in767_originalproof_dual_z s * G s).trace.re) =
      2 * (in767_originalproof_dual_p 3).trace.re +
        ((in767_originalproof_dual_p 1 - in767_originalproof_dual_p 3) * M 0).trace.re +
        ((in767_originalproof_dual_p 0 - in767_originalproof_dual_p 3) * M 1).trace.re +
        ((in767_originalproof_dual_p 2 - in767_originalproof_dual_p 3) * M 2).trace.re := by
    calc
      _ = ∑ s, (2 * (in767_originalproof_dual_p 3 * G s).trace.re +
          (if s 0 then ((in767_originalproof_dual_p 1 - in767_originalproof_dual_p 3) * G s).trace.re else 0) +
          (if s 1 then ((in767_originalproof_dual_p 0 - in767_originalproof_dual_p 3) * G s).trace.re else 0) +
          (if s 2 then ((in767_originalproof_dual_p 2 - in767_originalproof_dual_p 3) * G s).trace.re else 0)) := by
        exact Finset.sum_congr rfl fun s _ => hsplit s
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [← in767_originalproof_trace_matrix_sum, hsum, Matrix.mul_one]
        rw [hmargin _ 0, hmargin _ 1, hmargin _ 2]
  have hnonneg : 0 ≤ ∑ s, (in767_originalproof_dual_z s * G s).trace.re :=
    Finset.sum_nonneg fun s _ => in767_originalproof_trace_psd (in767_originalproof_dual_all_psd s) (hG s)
  rw [heq] at hnonneg
  have := hcert
  linarith


private lemma in767_originalproof_original_dual_term0 : ((in767_originalproof_dual_p 1 - in767_originalproof_dual_p 3) * ppt_qutrit_steered_effect 0).trace.re < -(1/1000 : ℝ) := by
  simp only [in767_originalproof_dual_p, in767_originalproof_dual_vec1, in767_originalproof_dual_vec3,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.sub_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, Fin.sum_univ_three]
  simp only [ppt_qutrit_steered_effect, ppt_qutrit_steered_normalizer,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  norm_num [ppt_qutrit_steered_unnormalized_effect, ppt_qutrit_bell_state,
    ppt_qutrit_bell_setting, ppt_qutrit_bell_vector,
    Matrix.vecMulVec_apply, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.vecHead, Matrix.vecTail, Pi.star_apply, Fin.sum_univ_three, Fin.sum_univ_four,
    map_div₀, map_ofNat]
  simp only [show (0 : Fin 3) ≠ 1 from by decide, show (0 : Fin 3) ≠ 2 from by decide,
    show (1 : Fin 3) ≠ 0 from by decide, show (1 : Fin 3) ≠ 2 from by decide,
    show (2 : Fin 3) ≠ 0 from by decide, show (2 : Fin 3) ≠ 1 from by decide,
    show (0 : Fin 4) ≠ 1 from by decide, show (0 : Fin 4) ≠ 2 from by decide, show (0 : Fin 4) ≠ 3 from by decide,
    show (1 : Fin 4) ≠ 0 from by decide, show (1 : Fin 4) ≠ 2 from by decide, show (1 : Fin 4) ≠ 3 from by decide,
    show (2 : Fin 4) ≠ 0 from by decide, show (2 : Fin 4) ≠ 1 from by decide, show (2 : Fin 4) ≠ 3 from by decide,
    show (3 : Fin 4) ≠ 0 from by decide, show (3 : Fin 4) ≠ 1 from by decide, show (3 : Fin 4) ≠ 2 from by decide,
    if_false, if_true] at *
  all_goals norm_num [ppt_qutrit_bell_vector, Matrix.vecMulVec_apply, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.vecHead, Matrix.vecTail, Pi.star_apply, map_div₀, map_ofNat]
  all_goals try simp only [show (0 : Fin 3) ≠ 1 from by decide, show (0 : Fin 3) ≠ 2 from by decide,
    show (1 : Fin 3) ≠ 0 from by decide, show (1 : Fin 3) ≠ 2 from by decide,
    show (2 : Fin 3) ≠ 0 from by decide, show (2 : Fin 3) ≠ 1 from by decide,
    show (0 : Fin 4) ≠ 1 from by decide, show (0 : Fin 4) ≠ 2 from by decide, show (0 : Fin 4) ≠ 3 from by decide,
    show (1 : Fin 4) ≠ 0 from by decide, show (1 : Fin 4) ≠ 2 from by decide, show (1 : Fin 4) ≠ 3 from by decide,
    show (2 : Fin 4) ≠ 0 from by decide, show (2 : Fin 4) ≠ 1 from by decide, show (2 : Fin 4) ≠ 3 from by decide,
    show (3 : Fin 4) ≠ 0 from by decide, show (3 : Fin 4) ≠ 1 from by decide, show (3 : Fin 4) ≠ 2 from by decide,
    if_false, if_true] at *
  all_goals norm_num [ppt_qutrit_bell_vector, Matrix.vecMulVec_apply, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.vecHead, Matrix.vecTail, Pi.star_apply, map_div₀, map_ofNat]
  all_goals try simp only [show (0 : Fin 3) ≠ 1 from by decide, show (0 : Fin 3) ≠ 2 from by decide,
    show (1 : Fin 3) ≠ 0 from by decide, show (1 : Fin 3) ≠ 2 from by decide,
    show (2 : Fin 3) ≠ 0 from by decide, show (2 : Fin 3) ≠ 1 from by decide,
    show (0 : Fin 4) ≠ 1 from by decide, show (0 : Fin 4) ≠ 2 from by decide, show (0 : Fin 4) ≠ 3 from by decide,
    show (1 : Fin 4) ≠ 0 from by decide, show (1 : Fin 4) ≠ 2 from by decide, show (1 : Fin 4) ≠ 3 from by decide,
    show (2 : Fin 4) ≠ 0 from by decide, show (2 : Fin 4) ≠ 1 from by decide, show (2 : Fin 4) ≠ 3 from by decide,
    show (3 : Fin 4) ≠ 0 from by decide, show (3 : Fin 4) ≠ 1 from by decide, show (3 : Fin 4) ≠ 2 from by decide,
    if_false, if_true] at *
  all_goals norm_num [ppt_qutrit_bell_vector, Matrix.vecMulVec_apply, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.vecHead, Matrix.vecTail, Pi.star_apply, map_div₀, map_ofNat]
  all_goals num_ineq

private lemma in767_originalproof_original_dual_term1 : ((in767_originalproof_dual_p 0 - in767_originalproof_dual_p 3) * ppt_qutrit_steered_effect 1).trace.re < -(1/1000 : ℝ) := by
  simp only [in767_originalproof_dual_p, in767_originalproof_dual_vec0, in767_originalproof_dual_vec3,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.sub_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, Fin.sum_univ_three]
  simp only [ppt_qutrit_steered_effect, ppt_qutrit_steered_normalizer,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  norm_num [ppt_qutrit_steered_unnormalized_effect, ppt_qutrit_bell_state,
    ppt_qutrit_bell_setting, ppt_qutrit_bell_vector,
    Matrix.vecMulVec_apply, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.vecHead, Matrix.vecTail, Pi.star_apply, Fin.sum_univ_three, Fin.sum_univ_four,
    map_div₀, map_ofNat]
  simp only [show (0 : Fin 3) ≠ 1 from by decide, show (0 : Fin 3) ≠ 2 from by decide,
    show (1 : Fin 3) ≠ 0 from by decide, show (1 : Fin 3) ≠ 2 from by decide,
    show (2 : Fin 3) ≠ 0 from by decide, show (2 : Fin 3) ≠ 1 from by decide,
    show (0 : Fin 4) ≠ 1 from by decide, show (0 : Fin 4) ≠ 2 from by decide, show (0 : Fin 4) ≠ 3 from by decide,
    show (1 : Fin 4) ≠ 0 from by decide, show (1 : Fin 4) ≠ 2 from by decide, show (1 : Fin 4) ≠ 3 from by decide,
    show (2 : Fin 4) ≠ 0 from by decide, show (2 : Fin 4) ≠ 1 from by decide, show (2 : Fin 4) ≠ 3 from by decide,
    show (3 : Fin 4) ≠ 0 from by decide, show (3 : Fin 4) ≠ 1 from by decide, show (3 : Fin 4) ≠ 2 from by decide,
    if_false, if_true] at *
  all_goals norm_num [ppt_qutrit_bell_vector, Matrix.vecMulVec_apply, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.vecHead, Matrix.vecTail, Pi.star_apply, map_div₀, map_ofNat]
  all_goals try simp only [show (0 : Fin 3) ≠ 1 from by decide, show (0 : Fin 3) ≠ 2 from by decide,
    show (1 : Fin 3) ≠ 0 from by decide, show (1 : Fin 3) ≠ 2 from by decide,
    show (2 : Fin 3) ≠ 0 from by decide, show (2 : Fin 3) ≠ 1 from by decide,
    show (0 : Fin 4) ≠ 1 from by decide, show (0 : Fin 4) ≠ 2 from by decide, show (0 : Fin 4) ≠ 3 from by decide,
    show (1 : Fin 4) ≠ 0 from by decide, show (1 : Fin 4) ≠ 2 from by decide, show (1 : Fin 4) ≠ 3 from by decide,
    show (2 : Fin 4) ≠ 0 from by decide, show (2 : Fin 4) ≠ 1 from by decide, show (2 : Fin 4) ≠ 3 from by decide,
    show (3 : Fin 4) ≠ 0 from by decide, show (3 : Fin 4) ≠ 1 from by decide, show (3 : Fin 4) ≠ 2 from by decide,
    if_false, if_true] at *
  all_goals norm_num [ppt_qutrit_bell_vector, Matrix.vecMulVec_apply, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.vecHead, Matrix.vecTail, Pi.star_apply, map_div₀, map_ofNat]
  all_goals try simp only [show (0 : Fin 3) ≠ 1 from by decide, show (0 : Fin 3) ≠ 2 from by decide,
    show (1 : Fin 3) ≠ 0 from by decide, show (1 : Fin 3) ≠ 2 from by decide,
    show (2 : Fin 3) ≠ 0 from by decide, show (2 : Fin 3) ≠ 1 from by decide,
    show (0 : Fin 4) ≠ 1 from by decide, show (0 : Fin 4) ≠ 2 from by decide, show (0 : Fin 4) ≠ 3 from by decide,
    show (1 : Fin 4) ≠ 0 from by decide, show (1 : Fin 4) ≠ 2 from by decide, show (1 : Fin 4) ≠ 3 from by decide,
    show (2 : Fin 4) ≠ 0 from by decide, show (2 : Fin 4) ≠ 1 from by decide, show (2 : Fin 4) ≠ 3 from by decide,
    show (3 : Fin 4) ≠ 0 from by decide, show (3 : Fin 4) ≠ 1 from by decide, show (3 : Fin 4) ≠ 2 from by decide,
    if_false, if_true] at *
  all_goals norm_num [ppt_qutrit_bell_vector, Matrix.vecMulVec_apply, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.vecHead, Matrix.vecTail, Pi.star_apply, map_div₀, map_ofNat]
  all_goals num_ineq

private lemma in767_originalproof_original_dual_term2 : ((in767_originalproof_dual_p 2 - in767_originalproof_dual_p 3) * ppt_qutrit_steered_effect 2).trace.re < -(1/1000 : ℝ) := by
  simp only [in767_originalproof_dual_p, in767_originalproof_dual_vec2, in767_originalproof_dual_vec3,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.sub_apply,
    Matrix.vecMulVec_apply, Pi.star_apply, Fin.sum_univ_three]
  simp only [ppt_qutrit_steered_effect, ppt_qutrit_steered_normalizer,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  norm_num [ppt_qutrit_steered_unnormalized_effect, ppt_qutrit_bell_state,
    ppt_qutrit_bell_setting, ppt_qutrit_bell_vector,
    Matrix.vecMulVec_apply, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.vecHead, Matrix.vecTail, Pi.star_apply, Fin.sum_univ_three, Fin.sum_univ_four,
    map_div₀, map_ofNat]
  simp only [show (0 : Fin 3) ≠ 1 from by decide, show (0 : Fin 3) ≠ 2 from by decide,
    show (1 : Fin 3) ≠ 0 from by decide, show (1 : Fin 3) ≠ 2 from by decide,
    show (2 : Fin 3) ≠ 0 from by decide, show (2 : Fin 3) ≠ 1 from by decide,
    show (0 : Fin 4) ≠ 1 from by decide, show (0 : Fin 4) ≠ 2 from by decide, show (0 : Fin 4) ≠ 3 from by decide,
    show (1 : Fin 4) ≠ 0 from by decide, show (1 : Fin 4) ≠ 2 from by decide, show (1 : Fin 4) ≠ 3 from by decide,
    show (2 : Fin 4) ≠ 0 from by decide, show (2 : Fin 4) ≠ 1 from by decide, show (2 : Fin 4) ≠ 3 from by decide,
    show (3 : Fin 4) ≠ 0 from by decide, show (3 : Fin 4) ≠ 1 from by decide, show (3 : Fin 4) ≠ 2 from by decide,
    if_false, if_true] at *
  all_goals norm_num [ppt_qutrit_bell_vector, Matrix.vecMulVec_apply, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.vecHead, Matrix.vecTail, Pi.star_apply, map_div₀, map_ofNat]
  all_goals try simp only [show (0 : Fin 3) ≠ 1 from by decide, show (0 : Fin 3) ≠ 2 from by decide,
    show (1 : Fin 3) ≠ 0 from by decide, show (1 : Fin 3) ≠ 2 from by decide,
    show (2 : Fin 3) ≠ 0 from by decide, show (2 : Fin 3) ≠ 1 from by decide,
    show (0 : Fin 4) ≠ 1 from by decide, show (0 : Fin 4) ≠ 2 from by decide, show (0 : Fin 4) ≠ 3 from by decide,
    show (1 : Fin 4) ≠ 0 from by decide, show (1 : Fin 4) ≠ 2 from by decide, show (1 : Fin 4) ≠ 3 from by decide,
    show (2 : Fin 4) ≠ 0 from by decide, show (2 : Fin 4) ≠ 1 from by decide, show (2 : Fin 4) ≠ 3 from by decide,
    show (3 : Fin 4) ≠ 0 from by decide, show (3 : Fin 4) ≠ 1 from by decide, show (3 : Fin 4) ≠ 2 from by decide,
    if_false, if_true] at *
  all_goals norm_num [ppt_qutrit_bell_vector, Matrix.vecMulVec_apply, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.vecHead, Matrix.vecTail, Pi.star_apply, map_div₀, map_ofNat]
  all_goals try simp only [show (0 : Fin 3) ≠ 1 from by decide, show (0 : Fin 3) ≠ 2 from by decide,
    show (1 : Fin 3) ≠ 0 from by decide, show (1 : Fin 3) ≠ 2 from by decide,
    show (2 : Fin 3) ≠ 0 from by decide, show (2 : Fin 3) ≠ 1 from by decide,
    show (0 : Fin 4) ≠ 1 from by decide, show (0 : Fin 4) ≠ 2 from by decide, show (0 : Fin 4) ≠ 3 from by decide,
    show (1 : Fin 4) ≠ 0 from by decide, show (1 : Fin 4) ≠ 2 from by decide, show (1 : Fin 4) ≠ 3 from by decide,
    show (2 : Fin 4) ≠ 0 from by decide, show (2 : Fin 4) ≠ 1 from by decide, show (2 : Fin 4) ≠ 3 from by decide,
    show (3 : Fin 4) ≠ 0 from by decide, show (3 : Fin 4) ≠ 1 from by decide, show (3 : Fin 4) ≠ 2 from by decide,
    if_false, if_true] at *
  all_goals norm_num [ppt_qutrit_bell_vector, Matrix.vecMulVec_apply, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.vecHead, Matrix.vecTail, Pi.star_apply, map_div₀, map_ofNat]
  all_goals num_ineq


private theorem in767_originalproof_original_dual_negative :
    2 * (in767_originalproof_dual_p 3).trace.re +
      ((in767_originalproof_dual_p 1 - in767_originalproof_dual_p 3) * ppt_qutrit_steered_effect 0).trace.re +
      ((in767_originalproof_dual_p 0 - in767_originalproof_dual_p 3) * ppt_qutrit_steered_effect 1).trace.re +
      ((in767_originalproof_dual_p 2 - in767_originalproof_dual_p 3) * ppt_qutrit_steered_effect 2).trace.re < 0 := by
  have hconst : 2 * (in767_originalproof_dual_p 3).trace.re = (5929/2000000 : ℝ) := by
    simp only [in767_originalproof_dual_p, in767_originalproof_dual_vec3, Matrix.trace, Matrix.diag_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, Fin.sum_univ_three]
    norm_num [Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, map_div₀, map_ofNat]
  linarith [in767_originalproof_original_dual_term0, in767_originalproof_original_dual_term1, in767_originalproof_original_dual_term2]

private theorem in767_originalproof_original_not_joint :
    ¬ ∃ G : (Fin 3 → Bool) → Matrix (Fin 3) (Fin 3) ℂ,
      (∀ s, (G s).PosSemidef) ∧ (∑ s, G s = 1) ∧
      ∀ j : Fin 3, (∑ s, if s j then G s else 0) = ppt_qutrit_steered_effect j :=
  in767_originalproof_any_not_joint ppt_qutrit_steered_effect in767_originalproof_original_dual_negative

theorem ppt_qutrit_steered_effect_incompatible : ¬ ∃ G : (Fin 3 → Bool) → Matrix (Fin 3) (Fin 3) ℂ, (∀ s, (G s).PosSemidef) ∧ (∑ s, G s = 1) ∧ ∀ j : Fin 3, (∑ s, if s j then G s else 0) = ppt_qutrit_steered_effect j := by
  exact in767_originalproof_original_not_joint

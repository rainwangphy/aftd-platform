import AFTD.Prelude
import AFTD.Kb.Tcs.PptQutritRationalBinaryEffect

/-!
# ppt_qutrit_rational_binary_effect_incompatible

Topic: quantum   Node: 1b9703a915e1

Provenance: helper lemma. Helper for OP-693, derived from the Bell witness of arXiv:1405.4502; rational matrices and exact dual certificates in experiments 22874, 22875, 22880, and 22905.

The three explicit rational qutrit effects have no joint positive parent.
-/

open Matrix
open scoped ComplexOrder Matrix BigOperators
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
private noncomputable def in767_witness_effect0 : Matrix (Fin 3) (Fin 3) ℂ := !![(1215916159000 / 21192203043001), (-2086398000000 / 21192203043001), (1071090000 / 65981951167); (-2086398000000 / 21192203043001), (3622358659000 / 21192203043001), (532050000 / 65981951167); (1071090000 / 65981951167), (532050000 / 65981951167), (7650594020 / 10066309561)]
private noncomputable def in767_witness_effect1 : Matrix (Fin 3) (Fin 3) ℂ := !![(316737473028500 / 1360728454130809), 0, 0; 0, (605951028500 / 1360728454130809), (-76179480000 / 4236629775103); 0, (-76179480000 / 4236629775103), (488260819680 / 646346857849)]
private noncomputable def in767_witness_effect2 : Matrix (Fin 3) (Fin 3) ℂ := !![(1215916159000 / 21192203043001), (2086398000000 / 21192203043001), (-1071090000 / 65981951167); (2086398000000 / 21192203043001), (3622358659000 / 21192203043001), (532050000 / 65981951167); (-1071090000 / 65981951167), (532050000 / 65981951167), (7650594020 / 10066309561)]
private noncomputable def in767_witness_rational_effect (j : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  if j = 0 then in767_witness_effect0 else if j = 1 then in767_witness_effect1 else in767_witness_effect2
open scoped MatrixOrder
private lemma in767_witness_trace_psd {n : Type} [Fintype n] [DecidableEq n] {P ρ : Matrix n n ℂ}
    (hP : P.PosSemidef) (hρ : ρ.PosSemidef) : 0 ≤ (P * ρ).trace.re := by
  obtain ⟨X, hX, -, rfl⟩ := CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hP.isHermitian
    (QuasispectrumRestricts.nnreal_of_nonneg hP.nonneg)
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, ← Matrix.mul_assoc]
  have h := hρ.mul_mul_conjTranspose_same X
  rw [← Matrix.star_eq_conjTranspose, hX.star_eq] at h
  exact (Complex.nonneg_iff.1 h.trace_nonneg).1

private noncomputable def in767_witness_dual_vec (i : Fin 4) : Fin 3 → ℂ :=
  if i = 0 then ![10599/1557500, 1791231/3115000, 1991/89000]
  else if i = 1 then ![-773727/1557500, -448691/1557500, 3993/178000]
  else if i = 2 then ![1565119/3115000, -455757/1557500, 1947/89000]
  else ![0, 0, 77/2000]

private lemma in767_witness_dual_vec0 : in767_witness_dual_vec 0 = ![10599/1557500, 1791231/3115000, 1991/89000] := by norm_num [in767_witness_dual_vec]
private lemma in767_witness_dual_vec1 : in767_witness_dual_vec 1 = ![-773727/1557500, -448691/1557500, 3993/178000] := by norm_num [in767_witness_dual_vec]
private lemma in767_witness_dual_vec2 : in767_witness_dual_vec 2 = ![1565119/3115000, -455757/1557500, 1947/89000] := by simp only [in767_witness_dual_vec, show (2 : Fin 4) ≠ 0 from by decide, show (2 : Fin 4) ≠ 1 from by decide, if_false, if_true]
private lemma in767_witness_dual_vec3 : in767_witness_dual_vec 3 = ![0, 0, 77/2000] := by simp only [in767_witness_dual_vec, show (3 : Fin 4) ≠ 0 from by decide, show (3 : Fin 4) ≠ 1 from by decide, show (3 : Fin 4) ≠ 2 from by decide, if_false]

private noncomputable def in767_witness_dual_p (i : Fin 4) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.vecMulVec (in767_witness_dual_vec i) (star (in767_witness_dual_vec i))

private noncomputable def in767_witness_dual_z (s : Fin 3 → Bool) : Matrix (Fin 3) (Fin 3) ℂ :=
  (2 : ℝ) • in767_witness_dual_p 3 + (if s 0 then in767_witness_dual_p 1 - in767_witness_dual_p 3 else 0) +
  (if s 1 then in767_witness_dual_p 0 - in767_witness_dual_p 3 else 0) +
  (if s 2 then in767_witness_dual_p 2 - in767_witness_dual_p 3 else 0)

private lemma in767_witness_dual_p_psd (i : Fin 4) : (in767_witness_dual_p i).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star _

private lemma in767_witness_dual_all_psd (s : Fin 3 → Bool) : (in767_witness_dual_z s).PosSemidef := by
  cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2
  · have he : in767_witness_dual_z s = in767_witness_dual_p 3 + in767_witness_dual_p 3 := by simp [in767_witness_dual_z, h0, h1, h2, two_smul] <;> abel
    rw [he]; exact (in767_witness_dual_p_psd 3).add (in767_witness_dual_p_psd 3)
  · have he : in767_witness_dual_z s = in767_witness_dual_p 2 + in767_witness_dual_p 3 := by simp [in767_witness_dual_z, h0, h1, h2, two_smul] <;> abel
    rw [he]; exact (in767_witness_dual_p_psd 2).add (in767_witness_dual_p_psd 3)
  · have he : in767_witness_dual_z s = in767_witness_dual_p 0 + in767_witness_dual_p 3 := by simp [in767_witness_dual_z, h0, h1, h2, two_smul] <;> abel
    rw [he]; exact (in767_witness_dual_p_psd 0).add (in767_witness_dual_p_psd 3)
  · have he : in767_witness_dual_z s = in767_witness_dual_p 0 + in767_witness_dual_p 2 := by simp [in767_witness_dual_z, h0, h1, h2, two_smul] <;> abel
    rw [he]; exact (in767_witness_dual_p_psd 0).add (in767_witness_dual_p_psd 2)
  · have he : in767_witness_dual_z s = in767_witness_dual_p 1 + in767_witness_dual_p 3 := by simp [in767_witness_dual_z, h0, h1, h2, two_smul] <;> abel
    rw [he]; exact (in767_witness_dual_p_psd 1).add (in767_witness_dual_p_psd 3)
  · have he : in767_witness_dual_z s = in767_witness_dual_p 1 + in767_witness_dual_p 2 := by simp [in767_witness_dual_z, h0, h1, h2, two_smul] <;> abel
    rw [he]; exact (in767_witness_dual_p_psd 1).add (in767_witness_dual_p_psd 2)
  · have he : in767_witness_dual_z s = in767_witness_dual_p 0 + in767_witness_dual_p 1 := by simp [in767_witness_dual_z, h0, h1, h2, two_smul] <;> abel
    rw [he]; exact (in767_witness_dual_p_psd 0).add (in767_witness_dual_p_psd 1)
  · let v : Fin 3 → ℂ := ![3533/5000, 0, 0]
    let w : Fin 3 → ℂ := ![0, 3533/5000, 0]
    have he : in767_witness_dual_z s = Matrix.vecMulVec v (star v) + Matrix.vecMulVec w (star w) := by
      simp only [in767_witness_dual_z, h0, h1, h2, if_true, in767_witness_dual_p,
        in767_witness_dual_vec0, in767_witness_dual_vec1, in767_witness_dual_vec2, in767_witness_dual_vec3, two_smul]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.vecMulVec_apply, Pi.star_apply] <;>
        norm_num [v, w, map_div₀, map_ofNat]
    rw [he]
    exact (Matrix.posSemidef_vecMulVec_self_star v).add (Matrix.posSemidef_vecMulVec_self_star w)

private lemma in767_witness_rational_dual_number :
    (2 * (in767_witness_dual_p 3).trace.re +
      ((in767_witness_dual_p 1 - in767_witness_dual_p 3) * in767_witness_effect0).trace.re +
      ((in767_witness_dual_p 0 - in767_witness_dual_p 3) * in767_witness_effect1).trace.re +
      ((in767_witness_dual_p 2 - in767_witness_dual_p 3) * in767_witness_effect2).trace.re) < 0 := by
  simp only [in767_witness_dual_p, in767_witness_dual_vec0, in767_witness_dual_vec1, in767_witness_dual_vec2, in767_witness_dual_vec3]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.sub_apply, Matrix.vecMulVec_apply, Pi.star_apply, Fin.sum_univ_succ]
  norm_num [in767_witness_effect0, in767_witness_effect1, in767_witness_effect2, Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Matrix.mul_apply, Matrix.sub_apply, Matrix.vecMulVec_apply, Pi.star_apply, Fin.sum_univ_succ, map_div₀, map_ofNat]

private lemma in767_witness_trace_matrix_sum (A : Matrix (Fin 3) (Fin 3) ℂ)
    (G : (Fin 3 → Bool) → Matrix (Fin 3) (Fin 3) ℂ) :
    (A * ∑ s, G s).trace.re = ∑ s, (A * G s).trace.re := by
  simp only [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]

private theorem in767_witness_rational_not_joint :
    ¬ ∃ G : (Fin 3 → Bool) → Matrix (Fin 3) (Fin 3) ℂ,
      (∀ s, (G s).PosSemidef) ∧ (∑ s, G s = 1) ∧
      ∀ j : Fin 3, (∑ s, if s j then G s else 0) = in767_witness_rational_effect j := by
  classical
  rintro ⟨G, hG, hsum, hmarg⟩
  have hmargin (A : Matrix (Fin 3) (Fin 3) ℂ) (j : Fin 3) :
      (∑ s, if s j then (A * G s).trace.re else 0) = (A * in767_witness_rational_effect j).trace.re := by
    rw [← hmarg j, in767_witness_trace_matrix_sum]
    apply Finset.sum_congr rfl
    intro s _
    split_ifs <;> simp_all
  have hsplit (s : Fin 3 → Bool) :
      (in767_witness_dual_z s * G s).trace.re =
        2 * (in767_witness_dual_p 3 * G s).trace.re +
        (if s 0 then ((in767_witness_dual_p 1 - in767_witness_dual_p 3) * G s).trace.re else 0) +
        (if s 1 then ((in767_witness_dual_p 0 - in767_witness_dual_p 3) * G s).trace.re else 0) +
        (if s 2 then ((in767_witness_dual_p 2 - in767_witness_dual_p 3) * G s).trace.re else 0) := by
    cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;>
      simp [in767_witness_dual_z, h0, h1, h2, two_smul, Matrix.add_mul, Matrix.sub_mul, Matrix.trace_add, Matrix.trace_sub] <;> ring
  have heq : (∑ s, (in767_witness_dual_z s * G s).trace.re) =
      2 * (in767_witness_dual_p 3).trace.re +
        ((in767_witness_dual_p 1 - in767_witness_dual_p 3) * in767_witness_effect0).trace.re +
        ((in767_witness_dual_p 0 - in767_witness_dual_p 3) * in767_witness_effect1).trace.re +
        ((in767_witness_dual_p 2 - in767_witness_dual_p 3) * in767_witness_effect2).trace.re := by
    calc
      _ = ∑ s, (2 * (in767_witness_dual_p 3 * G s).trace.re +
          (if s 0 then ((in767_witness_dual_p 1 - in767_witness_dual_p 3) * G s).trace.re else 0) +
          (if s 1 then ((in767_witness_dual_p 0 - in767_witness_dual_p 3) * G s).trace.re else 0) +
          (if s 2 then ((in767_witness_dual_p 2 - in767_witness_dual_p 3) * G s).trace.re else 0)) := by
        exact Finset.sum_congr rfl fun s _ => hsplit s
      _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [← in767_witness_trace_matrix_sum, hsum, Matrix.mul_one]
        rw [hmargin _ 0, hmargin _ 1, hmargin _ 2]
        simp [in767_witness_rational_effect]
  have hnonneg : 0 ≤ ∑ s, (in767_witness_dual_z s * G s).trace.re :=
    Finset.sum_nonneg fun s _ => in767_witness_trace_psd (in767_witness_dual_all_psd s) (hG s)
  rw [heq] at hnonneg
  have := in767_witness_rational_dual_number
  linarith

theorem ppt_qutrit_rational_binary_effect_incompatible :
  ¬ ∃ G : (Fin 3 → Bool) → Matrix (Fin 3) (Fin 3) ℂ,
    (∀ s, (G s).PosSemidef) ∧ (∑ s, G s = 1) ∧
    ∀ j : Fin 3, (∑ s, if s j then G s else 0) = ppt_qutrit_rational_binary_effect j := by
  exact in767_witness_rational_not_joint

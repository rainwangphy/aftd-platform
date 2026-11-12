import AFTD.Prelude
import AFTD.Kb.Tcs.SubspaceIncompatibleFamilyOfMicData
import AFTD.Kb.Tcs.F

/-!
# rank_two_frame_compression_no_parent

Topic: quantum   Node: f16ea1569ad8

Provenance: helper lemma. Helper excluding a four-outcome rank-one-frame construction for OP-693; exact compressed matrices in experiment 22918.

For r greater than one, no positive 2-by-2 parent has the displayed total matrix and three displayed marginals.
-/

open Matrix
open scoped ComplexOrder Matrix BigOperators
set_option maxHeartbeats 4000000
private noncomputable def in767_F0 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 1; 1, 1]
private noncomputable def in767_F2 : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 0, 1]
private noncomputable def in767_F3 : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]
private noncomputable def in767_FS : Matrix (Fin 2) (Fin 2) ℂ := !![2, 1; 1, 2]

private noncomputable def in767_v0 : Fin 2 → ℂ := ![1,1]
private noncomputable def in767_v2 : Fin 2 → ℂ := ![0,1]
private noncomputable def in767_v3 : Fin 2 → ℂ := ![1,0]

private lemma in767_outer0 : vecMulVec in767_v0 (star in767_v0) = in767_F0 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [vecMulVec_apply,in767_v0,in767_F0]
private lemma in767_outer2 : vecMulVec in767_v2 (star in767_v2) = in767_F2 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [vecMulVec_apply,in767_v2,in767_F2]
private lemma in767_outer3 : vecMulVec in767_v3 (star in767_v3) = in767_F3 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [vecMulVec_apply,in767_v3,in767_F3]

private lemma in767_Ssub : in767_FS - 1 = in767_F0 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [in767_FS,in767_F0,Matrix.one_apply]
private lemma in767_Isub : (1 : Matrix (Fin 2) (Fin 2) ℂ) - in767_F3 = in767_F2 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [in767_F3,in767_F2,Matrix.one_apply]

private theorem in767_frame_no_parent (r : ℝ) (hr : 1 < r) :
  ¬ ∃ G : (Fin 3 → Bool) → Matrix (Fin 2) (Fin 2) ℂ,
    (∀ s, (G s).PosSemidef) ∧
    (∑ s, G s = in767_FS) ∧
    (∑ s, if s 0 then G s else 0) = in767_F3 ∧
    (∑ s, if s 1 then G s else 0) = 1 ∧
    (∑ s, if s 2 then G s else 0) = (1/2 : ℝ) • (in767_FS - r • in767_F0) := by
  classical
  rintro ⟨G, hG, hsum, h0, h1, h2⟩
  have h0le : ∀ s, s 0 = true → (in767_F3 - G s).PosSemidef := by
    intro s hs
    have he := h0
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s), if_pos hs] at he
    rw [← he, add_sub_cancel_left]
    exact Matrix.posSemidef_sum _ fun a _ => by
      split_ifs
      · exact hG a
      · exact Matrix.PosSemidef.zero
  let F : (Fin 3 → Bool) → Matrix (Fin 2) (Fin 2) ℂ := fun s => if s 1 then 0 else G s
  have hFsum : ∑ s, F s = in767_F0 := by
    calc
      ∑ s, F s = (∑ s, G s) - ∑ s, (if s 1 then G s else 0) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun s _ => ?_
        cases hs : s 1 <;> simp [F,hs]
      _ = in767_F0 := by rw [hsum,h1,in767_Ssub]
  have h1le : ∀ s, s 1 = false → (in767_F0 - G s).PosSemidef := by
    intro s hs
    have he := hFsum
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s)] at he
    simp only [F,hs,Bool.false_eq_true,if_false] at he
    rw [← he, add_sub_cancel_left]
    exact Matrix.posSemidef_sum _ fun a _ => by
      split_ifs
      · exact Matrix.PosSemidef.zero
      · exact hG a
  have hzero : ∀ s, s 0 = true → s 1 = false → G s = 0 := by
    intro s hs0 hs1
    have hA := h0le s hs0
    have hB := h1le s hs1
    rw [← in767_outer3] at hA
    rw [← in767_outer0] at hB
    obtain ⟨a, ha, ea⟩ := rank_one_psd_dominated_eq_smul (G s) in767_v3 (hG s) hA
    obtain ⟨b, hb, eb⟩ := rank_one_psd_dominated_eq_smul (G s) in767_v0 (hG s) hB
    rw [in767_outer3] at ea
    rw [in767_outer0] at eb
    have e := congrArg (fun X : Matrix (Fin 2) (Fin 2) ℂ => (X 0 1).re) (ea.symm.trans eb)
    have hb0 : b = 0 := by simpa [in767_F0,in767_F3] using e.symm
    rw [eb, hb0, zero_smul]
  let R : (Fin 3 → Bool) → Matrix (Fin 2) (Fin 2) ℂ := fun s => if s 1 then (if s 0 then 0 else G s) else 0
  have hRsum : ∑ s, R s = in767_F2 := by
    calc
      ∑ s, R s = (∑ s, if s 1 then G s else 0) - ∑ s, (if s 0 then G s else 0) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun s _ => ?_
        by_cases hs0 : s 0 = true <;> by_cases hs1 : s 1 = true
        · simp [R,hs0,hs1]
        · have hz := hzero s hs0 (by simpa using hs1)
          simp [R,hs0,hs1,hz]
        · simp [R,hs0,hs1]
        · simp [R,hs0,hs1]
      _ = in767_F2 := by rw [h1,h0,in767_Isub]
  have h2le : ∀ s, s 0 = false → s 1 = true → (in767_F2 - G s).PosSemidef := by
    intro s hs0 hs1
    have he := hRsum
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s)] at he
    simp only [R,hs0,hs1,if_true,Bool.false_eq_true,if_false] at he
    rw [← he, add_sub_cancel_left]
    exact Matrix.posSemidef_sum _ fun a _ => by
      split_ifs
      · exact Matrix.PosSemidef.zero
      · exact hG a
      · exact Matrix.PosSemidef.zero
  have hentry : ∀ s, 0 ≤ (G s 0 1).re := by
    intro s
    by_cases hs0 : s 0 = true
    · have hA := h0le s hs0
      rw [← in767_outer3] at hA
      obtain ⟨a,ha,ea⟩ := rank_one_psd_dominated_eq_smul (G s) in767_v3 (hG s) hA
      rw [in767_outer3] at ea
      rw [ea]
      simp [in767_F3]
    · have hs0' : s 0 = false := by simpa using hs0
      by_cases hs1 : s 1 = true
      · have hA := h2le s hs0' hs1
        rw [← in767_outer2] at hA
        obtain ⟨a,ha,ea⟩ := rank_one_psd_dominated_eq_smul (G s) in767_v2 (hG s) hA
        rw [in767_outer2] at ea
        rw [ea]
        simp [in767_F2]
      · have hs1' : s 1 = false := by simpa using hs1
        have hA := h1le s hs1'
        rw [← in767_outer0] at hA
        obtain ⟨a,ha,ea⟩ := rank_one_psd_dominated_eq_smul (G s) in767_v0 (hG s) hA
        rw [in767_outer0] at ea
        rw [ea]
        simpa [in767_F0] using ha
  have hnonneg : 0 ≤ ((∑ s : (Fin 3 → Bool), if s 2 then G s else 0) 0 1).re := by
    simp only [Matrix.sum_apply, Complex.re_sum]
    exact Finset.sum_nonneg fun s _ => by split_ifs <;> simp_all
  rw [h2] at hnonneg
  norm_num [in767_FS,in767_F0] at hnonneg
  linarith

theorem rank_two_frame_compression_no_parent (r : ℝ) (hr : 1 < r) :
  ¬ ∃ G : (Fin 3 → Bool) → Matrix (Fin 2) (Fin 2) ℂ,
    (∀ s, (G s).PosSemidef) ∧
    (∑ s, G s = !![2, 1; 1, 2]) ∧
    (∑ s, if s 0 then G s else 0) = !![1, 0; 0, 0] ∧
    (∑ s, if s 1 then G s else 0) = 1 ∧
    (∑ s, if s 2 then G s else 0) =
      (1/2 : ℝ) • (!![2, 1; 1, 2] - r • !![1, 1; 1, 1]) := by
  exact in767_frame_no_parent r hr

import AFTD.Prelude
import AFTD.Kb.Tcs.BalancedBlowupMatrix

/-!
# balanced_blowup_spectrum_subset

Topic: graphs   Node: b5bb484ac7c3

Provenance: helper lemma. scout/2610-14100-digraph-laplacian-spectra-the-2005-polygon-conjecture-fails.md:1049

For natural numbers m and d with 1 ≤ d, and an m x m real matrix L on Fin m, the complex spectrum of L is a subset of the complex spectrum of its balanced blow-up matrix balanced_blowup_matrix m d L.
-/

/-- The spectrum of L is contained in the spectrum of its balanced blow-up matrix. -/
theorem balanced_blowup_spectrum_subset (m d : ℕ) (hd : 1 ≤ d) (L : Matrix (Fin m) (Fin m) ℝ) :
    spectrum ℂ (L.map Complex.ofReal) ⊆
      spectrum ℂ ((balanced_blowup_matrix m d L).map Complex.ofReal) := by
  intro r hr
  by_cases hm : m = 0
  · subst hm
    rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, Classical.not_not] at hr
    rw [Matrix.det_isEmpty] at hr
    exact False.elim (one_ne_zero hr)
  have hd_pos : (d : ℝ) ≠ 0 := by
    norm_cast
    omega
  have h_entry (i j : Fin m) (s : Fin d) (t : Fin d) :
      balanced_blowup_matrix m d L (i, s) (j, t) =
        (if i = j then L i i else 0) * (if s = t then 1 else 0) -
          (1 / (d : ℝ)) * (if i = j then 0 else - L i j) := by
    unfold balanced_blowup_matrix
    simp [Matrix.one_apply, Matrix.diagonal_apply]
  have sum_blowup_eq (i j : Fin m) (s : Fin d) :
      ∑ t : Fin d, ((balanced_blowup_matrix m d L).map Complex.ofReal) (i, s) (j, t) =
        (L.map Complex.ofReal) i j := by
    have h_sum : ∑ t : Fin d, balanced_blowup_matrix m d L (i, s) (j, t) = L i j := by
      simp_rw [h_entry, Finset.sum_sub_distrib]
      have h1 : (∑ t : Fin d, (if i = j then L i i else 0) * (if s = t then 1 else 0 : ℝ)) =
          (if i = j then L i i else 0) := by
        simp
      have hd_mul (x : ℝ) : d • (1 / (d : ℝ) * x) = x := by
        rw [nsmul_eq_mul, ← mul_assoc, mul_one_div_cancel hd_pos, one_mul]
      have h2 : (∑ _t : Fin d, (1 / (d : ℝ)) * (if i = j then 0 else - L i j)) =
          (if i = j then 0 else - L i j) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, hd_mul]
      rw [h1, h2]
      split_ifs with hij
      · subst hij; ring
      · ring
    change ∑ t : Fin d, (Complex.ofRealHom (balanced_blowup_matrix m d L (i, s) (j, t))) =
      Complex.ofRealHom (L i j)
    rw [← map_sum Complex.ofRealHom, h_sum]
  have has_eigen : ∃ v : Fin m → ℂ, v ≠ 0 ∧ Matrix.mulVec (L.map Complex.ofReal) v = r • v := by
    rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, Classical.not_not] at hr
    rw [← Matrix.exists_mulVec_eq_zero_iff] at hr
    obtain ⟨v, hv, h0⟩ := hr
    refine ⟨v, hv, ?_⟩
    ext i
    have hi : (Matrix.mulVec (algebraMap ℂ (Matrix (Fin m) (Fin m) ℂ) r - L.map Complex.ofReal) v) i = 0 :=
      congr_fun h0 i
    rw [Matrix.sub_mulVec] at hi
    simp only [Pi.sub_apply, sub_eq_zero] at hi
    have hdiag : (Matrix.mulVec (Matrix.diagonal ((algebraMap ℂ (Fin m → ℂ)) r)) v) i = r * v i := by
      simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
    rw [Matrix.algebraMap_eq_diagonal, hdiag] at hi
    simp [Pi.smul_apply, smul_eq_mul, hi]
  obtain ⟨v, hv, hLv⟩ := has_eigen
  let w : Fin m × Fin d → ℂ := fun p => v p.1
  have hw : w ≠ 0 := by
    intro hw0
    apply hv
    ext i
    have hd0 : 0 < d := by omega
    have hwi := congr_fun hw0 (i, ⟨0, hd0⟩)
    exact hwi
  have hBw : Matrix.mulVec ((balanced_blowup_matrix m d L).map Complex.ofReal) w = r • w := by
    ext ⟨i, s⟩
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, w]
    rw [Fintype.sum_prod_type]
    have h_inner (j : Fin m) :
        (∑ t : Fin d, ((balanced_blowup_matrix m d L).map Complex.ofReal) (i, s) (j, t) * v j) =
          (L.map Complex.ofReal) i j * v j := by
      rw [← Finset.sum_mul, sum_blowup_eq i j s]
    simp_rw [h_inner]
    have h_vi : (Matrix.mulVec (L.map Complex.ofReal) v) i = (r • v) i := congr_fun hLv i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h_vi
    exact h_vi
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, Classical.not_not]
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨w, hw, ?_⟩
  ext ⟨i, s⟩
  rw [Matrix.sub_mulVec]
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero]
  have hdiag : (Matrix.mulVec (Matrix.diagonal ((algebraMap ℂ (Fin m × Fin d → ℂ)) r)) w) (i, s) = r * w (i, s) := by
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
  rw [Matrix.algebraMap_eq_diagonal, hdiag]
  have hi : (Matrix.mulVec ((balanced_blowup_matrix m d L).map Complex.ofReal) w) (i, s) = (r • w) (i, s) :=
    congr_fun hBw (i, s)
  simp only [Pi.smul_apply, smul_eq_mul] at hi
  exact hi.symm

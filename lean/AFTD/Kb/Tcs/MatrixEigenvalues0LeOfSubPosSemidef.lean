import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Physics.IsSymmetric
import AFTD.Kb.Tcs.V

/-!
# matrix_eigenvalues₀_le_of_sub_posSemidef

Topic: information   Node: 98f2835cf883

Provenance: formalization of a published result. Source: scout/2610-10618-the-hellinger-conjecture-for-antipodal-boolean-functions.md:402

If $A$ and $C$ are real symmetric matrices such that $C - A$ is positive semidefinite, then each ordered eigenvalue of $A$ is at most the corresponding ordered eigenvalue of $C$.
-/

lemma matrix_eigenvalues₀_le_of_sub_posSemidef_aux_qf_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {N : ℕ} (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (hN : Module.finrank ℝ E = N)
    (S : Finset (Fin N)) (c : ℝ) (hc : ∀ k ∈ S, hT.eigenvalues hN k ≤ c)
    (v : E) (hv : ∀ k, k ∉ S → inner ℝ (hT.eigenvectorBasis hN k) v = 0) :
    inner ℝ (T v) v ≤ c * inner ℝ v v := by
  have qform : inner ℝ (T v) v = ∑ i : Fin N, hT.eigenvalues hN i * (inner ℝ (hT.eigenvectorBasis hN i) v)^2 := by
    rw [← OrthonormalBasis.sum_inner_mul_inner (hT.eigenvectorBasis hN) (T v) v]
    apply Finset.sum_congr rfl
    intro i _
    rw [hT v (hT.eigenvectorBasis hN i), hT.apply_eigenvectorBasis hN i, inner_smul_right]
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    rw [real_inner_comm v]
    ring
  have pars : inner ℝ v v = ∑ i : Fin N, (inner ℝ (hT.eigenvectorBasis hN i) v)^2 := by
    rw [← OrthonormalBasis.sum_inner_mul_inner (hT.eigenvectorBasis hN) v v]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm v]
    ring
  rw [qform, pars, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : k ∈ S
  · exact mul_le_mul_of_nonneg_right (hc k hk) (sq_nonneg _)
  · rw [hv k hk]; simp

lemma matrix_eigenvalues₀_le_of_sub_posSemidef_aux_qf_ge
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {N : ℕ} (T : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (hN : Module.finrank ℝ E = N)
    (S : Finset (Fin N)) (c : ℝ) (hc : ∀ k ∈ S, c ≤ hT.eigenvalues hN k)
    (v : E) (hv : ∀ k, k ∉ S → inner ℝ (hT.eigenvectorBasis hN k) v = 0) :
    c * inner ℝ v v ≤ inner ℝ (T v) v := by
  have qform : inner ℝ (T v) v = ∑ i : Fin N, hT.eigenvalues hN i * (inner ℝ (hT.eigenvectorBasis hN i) v)^2 := by
    rw [← OrthonormalBasis.sum_inner_mul_inner (hT.eigenvectorBasis hN) (T v) v]
    apply Finset.sum_congr rfl
    intro i _
    rw [hT v (hT.eigenvectorBasis hN i), hT.apply_eigenvectorBasis hN i, inner_smul_right]
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    rw [real_inner_comm v]
    ring
  have pars : inner ℝ v v = ∑ i : Fin N, (inner ℝ (hT.eigenvectorBasis hN i) v)^2 := by
    rw [← OrthonormalBasis.sum_inner_mul_inner (hT.eigenvectorBasis hN) v v]
    apply Finset.sum_congr rfl
    intro i _
    rw [real_inner_comm v]
    ring
  rw [qform, pars, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k _
  by_cases hk : k ∈ S
  · exact mul_le_mul_of_nonneg_right (hc k hk) (sq_nonneg _)
  · rw [hv k hk]; simp

lemma matrix_eigenvalues₀_le_of_sub_posSemidef_aux_eigen_mono
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {N : ℕ} (T S : E →ₗ[ℝ] E) (hT : T.IsSymmetric) (hS : S.IsSymmetric)
    (hN : Module.finrank ℝ E = N)
    (hq : ∀ v : E, inner ℝ (T v) v ≤ inner ℝ (S v) v) (j : Fin N) :
    hT.eigenvalues hN j ≤ hS.eigenvalues hN j := by
  set sT : Finset (Fin N) := Finset.Iic j with hsT
  set sS : Finset (Fin N) := Finset.Ici j with hsS
  set fT : {x // x ∈ sT} → E := fun x => (hT.eigenvectorBasis hN) x.val with hfT
  set fS : {x // x ∈ sS} → E := fun x => (hS.eigenvectorBasis hN) x.val with hfS
  set V : Submodule ℝ E := Submodule.span ℝ (Set.range fT) with hV
  set W : Submodule ℝ E := Submodule.span ℝ (Set.range fS) with hW
  have hbT0 : LinearIndependent ℝ ⇑(hT.eigenvectorBasis hN) := by
    simpa using (hT.eigenvectorBasis hN).toBasis.linearIndependent
  have hbS0 : LinearIndependent ℝ ⇑(hS.eigenvectorBasis hN) := by
    simpa using (hS.eigenvectorBasis hN).toBasis.linearIndependent
  have liT : LinearIndependent ℝ fT := by
    have h := hbT0.comp (fun x : {x // x ∈ sT} => x.val) Subtype.val_injective
    simpa [hfT, Function.comp_def] using h
  have liS : LinearIndependent ℝ fS := by
    have h := hbS0.comp (fun x : {x // x ∈ sS} => x.val) Subtype.val_injective
    simpa [hfS, Function.comp_def] using h
  have hcardT : Module.finrank ℝ ↥V = j.val + 1 := by
    rw [hV, finrank_span_eq_card liT, Fintype.card_coe, hsT]
    exact Fin.card_Iic j
  have hcardS : Module.finrank ℝ ↥W = N - j.val := by
    rw [hW, finrank_span_eq_card liS, Fintype.card_coe, hsS]
    exact Fin.card_Ici j
  have hne : V ⊓ W ≠ ⊥ := by
    intro hbot
    have hdim := Submodule.finrank_sup_add_finrank_inf_eq V W
    rw [hbot, finrank_bot, add_zero, hcardT, hcardS] at hdim
    have hle : Module.finrank ℝ ↥(V ⊔ W) ≤ N := by
      have h := Submodule.finrank_le (V ⊔ W); rwa [hN] at h
    have hj := j.isLt
    omega
  obtain ⟨v, hvVW, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  rw [Submodule.mem_inf] at hvVW
  obtain ⟨hvV, hvW⟩ := hvVW
  have horthT : ∀ k, k ∉ sT → inner ℝ ((hT.eigenvectorBasis hN) k) v = 0 := by
    intro k hk
    have hv : v ∈ Submodule.span ℝ (Set.range fT) := by rw [← hV]; exact hvV
    refine Submodule.span_induction
      (p := fun w _ => inner ℝ ((hT.eigenvectorBasis hN) k) w = 0) ?_ ?_ ?_ ?_ hv
    · rintro x ⟨y, rfl⟩
      simp only [hfT]
      have hy : (y : Fin N) ∈ sT := y.2
      have hne' : (y : Fin N) ≠ k := fun h => hk (h ▸ hy)
      rw [OrthonormalBasis.inner_eq_ite, if_neg (Ne.symm hne')]
    · simp
    · intro x y _ _ hx hy
      rw [inner_add_right, hx, hy, add_zero]
    · intro a x _ hx
      rw [inner_smul_right, hx, mul_zero]
  have horthS : ∀ k, k ∉ sS → inner ℝ ((hS.eigenvectorBasis hN) k) v = 0 := by
    intro k hk
    have hv : v ∈ Submodule.span ℝ (Set.range fS) := by rw [← hW]; exact hvW
    refine Submodule.span_induction
      (p := fun w _ => inner ℝ ((hS.eigenvectorBasis hN) k) w = 0) ?_ ?_ ?_ ?_ hv
    · rintro x ⟨y, rfl⟩
      simp only [hfS]
      have hy : (y : Fin N) ∈ sS := y.2
      have hne' : (y : Fin N) ≠ k := fun h => hk (h ▸ hy)
      rw [OrthonormalBasis.inner_eq_ite, if_neg (Ne.symm hne')]
    · simp
    · intro x y _ _ hx hy
      rw [inner_add_right, hx, hy, add_zero]
    · intro a x _ hx
      rw [inner_smul_right, hx, mul_zero]
  have hTV : hT.eigenvalues hN j * inner ℝ v v ≤ inner ℝ (T v) v := by
    refine matrix_eigenvalues₀_le_of_sub_posSemidef_aux_qf_ge T hT hN sT (hT.eigenvalues hN j) (fun k hk => ?_) v horthT
    exact hT.eigenvalues_antitone hN (Finset.mem_Iic.mp hk)
  have hSV : inner ℝ (S v) v ≤ hS.eigenvalues hN j * inner ℝ v v := by
    refine matrix_eigenvalues₀_le_of_sub_posSemidef_aux_qf_le S hS hN sS (hS.eigenvalues hN j) (fun k hk => ?_) v horthS
    exact hS.eigenvalues_antitone hN (Finset.mem_Ici.mp hk)
  have hpos : 0 < inner ℝ v v := real_inner_self_pos.mpr hvne
  have hmain : hT.eigenvalues hN j * inner ℝ v v ≤ hS.eigenvalues hN j * inner ℝ v v :=
    le_trans hTV (le_trans (hq v) hSV)
  exact le_of_mul_le_mul_right hmain hpos

/-- Adding a positive semidefinite matrix does not decrease any ordered eigenvalue. -/
theorem matrix_eigenvalues₀_le_of_sub_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    (A C : Matrix n n ℝ) (hA : A.IsHermitian) (hC : C.IsHermitian)
    (h_le : (C - A).PosSemidef) (j : Fin (Fintype.card n)) :
    hA.eigenvalues₀ j ≤ hC.eigenvalues₀ j := by
  have hq : ∀ v : EuclideanSpace ℝ n,
      inner ℝ (Matrix.toEuclideanLin A v) v ≤ inner ℝ (Matrix.toEuclideanLin C v) v := by
    intro v
    have hpos : (Matrix.toEuclideanLin (C - A)).IsPositive :=
      Matrix.isPositive_toEuclideanLin_iff.mpr h_le
    have h := hpos.inner_nonneg_left v
    have hsub : Matrix.toEuclideanLin (C - A)
        = Matrix.toEuclideanLin C - Matrix.toEuclideanLin A := by
      ext x
      simp
    rw [hsub, LinearMap.sub_apply, inner_sub_left] at h
    linarith
  have hmain := matrix_eigenvalues₀_le_of_sub_posSemidef_aux_eigen_mono
    (E := EuclideanSpace ℝ n) (N := Fintype.card n)
    (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin C)
    (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) (Matrix.isSymmetric_toEuclideanLin_iff.mpr hC)
    finrank_euclideanSpace hq j
  simpa [Matrix.IsHermitian.eigenvalues₀] using hmain

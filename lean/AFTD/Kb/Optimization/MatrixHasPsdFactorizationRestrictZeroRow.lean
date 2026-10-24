import AFTD.Prelude
import AFTD.Kb.Optimization.MatrixHasPsdFactorization

/-!
# matrix_has_psd_factorization_restrict_zero_row

Topic: integer_programming   Node: f2d94b396949

Provenance: formalization of a published result. Source: arXiv:2610.04498 Lemma 2.2 (facet case, in slack-matrix form)

Facet restriction lowers the PSD factorization size: if M has a PSD factorization of size r and row i₀ of M is not identically zero, then the submatrix of M on the columns where row i₀ vanishes (all rows kept) has a PSD factorization of size r − 1. For a slack matrix and i₀ a facet, this is the facet case of the face inequality xc_PSD(P) ≥ xc_PSD(F) + dim P − dim F.
-/

theorem matrix_pos_semidef_real_exists_gram {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ)
    (hB : B.PosSemidef) : ∃ G : Matrix (Fin r) (Fin r) ℝ, B = G.conjTranspose * G := by
  open scoped MatrixOrder in
  obtain ⟨X, hX, -, hXB⟩ :=
    sub_zero B ▸ CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hB.isHermitian
      (QuasispectrumRestricts.nnreal_of_nonneg hB.nonneg)
  have hXX : X.conjTranspose = X := hX
  exact ⟨X, by rw [hXX, hXB, sub_zero]⟩

theorem matrix_has_psd_factorization_restrict_zero_row {m n : Type*} (M : Matrix m n ℝ) (r : ℕ)
    (h : matrix_has_psd_factorization M r) (i₀ : m) (j₀ : n) (hj₀ : M i₀ j₀ ≠ 0) :
    matrix_has_psd_factorization (M.submatrix id (Subtype.val : {j // M i₀ j = 0} → n)) (r - 1) := by
  classical
  obtain ⟨A, B, hA, hB, hM⟩ := h
  set A₀ := A i₀ with hA₀def
  have hA₀ : A₀ ≠ 0 := by
    intro h0; apply hj₀; rw [hM, ← hA₀def, h0]; simp
  obtain ⟨k, hk⟩ : ∃ k, (fun l => A₀ l k) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hA₀
    ext l k'
    exact congrFun (hcon k') l
  set u : Fin r → ℝ := fun l => A₀ l k with hudef
  let φ : Module.Dual ℝ (Fin r → ℝ) :=
    { toFun := fun x => u ⬝ᵥ x
      map_add' := fun x y => dotProduct_add u x y
      map_smul' := fun c x => by simp [dotProduct_smul] }
  have hφ : φ ≠ 0 := by
    intro h0
    have h1 : u ⬝ᵥ u = 0 := by
      have := LinearMap.congr_fun h0 u
      simpa [φ] using this
    exact hk (dotProduct_self_eq_zero.1 h1)
  set H := LinearMap.ker φ
  have hfin : Module.finrank ℝ H = r - 1 := by
    have := Module.Dual.finrank_ker_add_one_of_ne_zero hφ
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
    exact Nat.eq_sub_of_add_eq this
  let bH : Module.Basis (Fin (r - 1)) ℝ H := Module.finBasisOfFinrankEq ℝ H hfin
  let U : Matrix (Fin r) (Fin (r - 1)) ℝ := fun l c => (bH c : Fin r → ℝ) l
  -- rows of a Gram factor of each B j in the zero set lie in H
  have hrow : ∀ j : {j // M i₀ j = 0}, ∃ Y : Matrix (Fin r) (Fin (r - 1)) ℝ,
      B j.1 = U * (Y.conjTranspose * Y) * U.conjTranspose := by
    intro j
    obtain ⟨G, hG⟩ := matrix_pos_semidef_real_exists_gram (B j.1) (hB j.1)
    have hsym : ∀ a b, A₀ a b = A₀ b a := by
      intro a b
      have := congrFun (congrFun (hA i₀).1 a) b
      simp [Matrix.conjTranspose_apply] at this
      first | exact this | exact this.symm
    have hmem : ∀ k', G k' ∈ H := by
      have h0 : (A₀ * (G.conjTranspose * G)).trace = 0 := by
        rw [← hG, ← hM]; exact j.2
      rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle] at h0
      have hnn : ∀ k', 0 ≤ (G * A₀ * G.conjTranspose) k' k' := by
        intro k'
        have := (hA i₀).conjTranspose_mul_mul_same G.conjTranspose
        rw [Matrix.conjTranspose_conjTranspose] at this
        exact this.diag_nonneg
      have hz : ∀ k', (G * A₀ * G.conjTranspose) k' k' = 0 := by
        intro k'
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun k'' _ => hnn k'')).1 h0 k' (Finset.mem_univ _)
        exact this
      intro k'
      have hq : star (G k') ⬝ᵥ Matrix.mulVec A₀ (G k') = 0 := by
        rw [← hz k']
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum,
          mul_comm, mul_left_comm]
        exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by rw [hsym]))
      have hv := ((hA i₀).dotProduct_mulVec_zero_iff (G k')).1 hq
      show u ⬝ᵥ G k' = 0
      have hsymm : ∀ l, A₀ l k = A₀ k l := by
        intro l
        have := congrFun (congrFun (hA i₀).1 k) l
        simp [Matrix.conjTranspose_apply] at this
        first | exact this | exact this.symm
      have := congrFun hv k
      simpa [hudef, hsymm, Matrix.mulVec, dotProduct] using this
    let Y : Matrix (Fin r) (Fin (r - 1)) ℝ := fun k' c => bH.repr ⟨G k', hmem k'⟩ c
    have hGY : G = Y * U.conjTranspose := by
      ext k' l
      have := bH.sum_repr ⟨G k', hmem k'⟩
      have h2 := congrArg (fun x : H => (x : Fin r → ℝ) l) this
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        smul_eq_mul] at h2
      rw [← h2, Matrix.mul_apply]
      exact Finset.sum_congr rfl (fun _ _ => rfl)
    refine ⟨Y, ?_⟩
    rw [hG, hGY, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  choose Y hY using hrow
  refine ⟨fun i => U.conjTranspose * A i * U, fun j => (Y j).conjTranspose * Y j,
    fun i => (hA i).conjTranspose_mul_mul_same U, fun j => Matrix.posSemidef_conjTranspose_mul_self _, ?_⟩
  intro i j
  simp only [Matrix.submatrix_apply, id]
  rw [hM, hY j]
  rw [show A i * (U * ((Y j).conjTranspose * Y j) * U.conjTranspose) = (A i * U * ((Y j).conjTranspose * Y j)) * U.conjTranspose by
    simp only [Matrix.mul_assoc]]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

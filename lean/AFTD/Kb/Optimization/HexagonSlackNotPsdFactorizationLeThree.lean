import AFTD.Prelude
import AFTD.Kb.Optimization.MatrixHasPsdFactorization

/-!
# hexagon_slack_not_psd_factorization_le_three

Topic: integer_programming   Node: 64890063e1a8

Provenance: formalization of a published result. Source: arXiv:2610.04498 Sec. 4.2 (the regular hexagon has PSD rank four, cited there as [15]); this is the slack matrix of the face Π₃ of Π_n

The slack matrix of the regular hexagon, the 6×6 circulant matrix with first row (0,0,1,2,2,1) (entry (i,j) = c(j−i mod 6)), has no positive semidefinite factorization of size at most 3; that is, the regular hexagon has PSD rank at least four.
-/

theorem hexagon_psd_gram_aux {r : ℕ} (B : Matrix (Fin r) (Fin r) ℝ)
    (hB : B.PosSemidef) : ∃ G : Matrix (Fin r) (Fin r) ℝ, B = G.conjTranspose * G := by
  open scoped MatrixOrder in
  obtain ⟨X, hX, -, hXB⟩ :=
    sub_zero B ▸ CFC.exists_sqrt_of_isSelfAdjoint_of_quasispectrumRestricts hB.isHermitian
      (QuasispectrumRestricts.nnreal_of_nonneg hB.nonneg)
  have hXX : X.conjTranspose = X := hX
  exact ⟨X, by rw [hXX, hXB, sub_zero]⟩

theorem matrix_has_psd_factorization_cross_of_le_one {m n : Type*} (M : Matrix m n ℝ) (s : ℕ)
    (hs : s ≤ 1) (h : matrix_has_psd_factorization M s) (i i' : m) (j j' : n) :
    M i j * M i' j' = M i j' * M i' j := by
  obtain ⟨A, B, -, -, hM⟩ := h
  interval_cases s
  · simp [hM, Matrix.trace]
  · simp only [hM, Matrix.trace_fin_one, Matrix.mul_apply, Fin.sum_univ_one]
    ring

theorem psd_factors_restrict_kernel {m n : Type*} {r : ℕ} (M : Matrix m n ℝ)
    (A : m → Matrix (Fin r) (Fin r) ℝ) (B : n → Matrix (Fin r) (Fin r) ℝ)
    (hA : ∀ i, (A i).PosSemidef) (hB : ∀ j, (B j).PosSemidef)
    (hM : ∀ i j, M i j = (A i * B j).trace) (i₀ : m) :
    matrix_has_psd_factorization (M.submatrix id (Subtype.val : {j // M i₀ j = 0} → n))
      (r - (A i₀).rank) := by
  classical
  set A₀ := A i₀ with hA₀def
  set H := LinearMap.ker (Matrix.mulVecLin A₀)
  have hfin : Module.finrank ℝ H = r - A₀.rank := by
    have := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin A₀)
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at this
    change A₀.rank + Module.finrank ℝ H = r at this
    omega
  let bH : Module.Basis (Fin (r - A₀.rank)) ℝ H := Module.finBasisOfFinrankEq ℝ H hfin
  let U : Matrix (Fin r) (Fin (r - A₀.rank)) ℝ := fun l c => (bH c : Fin r → ℝ) l
  have hrow : ∀ j : {j // M i₀ j = 0}, ∃ Y : Matrix (Fin r) (Fin (r - A₀.rank)) ℝ,
      B j.1 = U * (Y.conjTranspose * Y) * U.conjTranspose := by
    intro j
    obtain ⟨G, hG⟩ := hexagon_psd_gram_aux (B j.1) (hB j.1)
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
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun k'' _ => hnn k'')).1 h0 k' (Finset.mem_univ _)
      have hsym : ∀ a b, A₀ a b = A₀ b a := by
        intro a b
        have := congrFun (congrFun (hA i₀).1 a) b
        simp [Matrix.conjTranspose_apply] at this
        first | exact this | exact this.symm
      intro k'
      have hq : star (G k') ⬝ᵥ Matrix.mulVec A₀ (G k') = 0 := by
        rw [← hz k']
        simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]
        exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by rw [hsym]))
      have hv := ((hA i₀).dotProduct_mulVec_zero_iff (G k')).1 hq
      exact LinearMap.mem_ker.2 hv
    let Y : Matrix (Fin r) (Fin (r - A₀.rank)) ℝ := fun k' c => bH.repr ⟨G k', hmem k'⟩ c
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
    fun i => (hA i).conjTranspose_mul_mul_same U,
    fun j => Matrix.posSemidef_conjTranspose_mul_self _, ?_⟩
  intro i j
  simp only [Matrix.submatrix_apply, id]
  rw [hM, hY j]
  rw [show A i * (U * ((Y j).conjTranspose * Y j) * U.conjTranspose) =
      (A i * U * ((Y j).conjTranspose * Y j)) * U.conjTranspose by simp only [Matrix.mul_assoc]]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem psd_factor_rank_le_one_of_cross {m n : Type*} {r : ℕ} (hr : r ≤ 3) (M : Matrix m n ℝ)
    (A : m → Matrix (Fin r) (Fin r) ℝ) (B : n → Matrix (Fin r) (Fin r) ℝ)
    (hA : ∀ i, (A i).PosSemidef) (hB : ∀ j, (B j).PosSemidef)
    (hM : ∀ i j, M i j = (A i * B j).trace) (i₀ : m) (j₁ j₂ : n)
    (h₁ : M i₀ j₁ = 0) (h₂ : M i₀ j₂ = 0) (p q : m)
    (hpq : M p j₁ * M q j₂ ≠ M p j₂ * M q j₁) : (A i₀).rank ≤ 1 := by
  by_contra hcon
  push Not at hcon
  have hk := psd_factors_restrict_kernel M A B hA hB hM i₀
  have := matrix_has_psd_factorization_cross_of_le_one _ _ (by omega) hk p q ⟨j₁, h₁⟩ ⟨j₂, h₂⟩
  exact hpq (by simpa using this)

theorem psd_rank_le_one_eq_vecMulVec {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosSemidef)
    (h : A.rank ≤ 1) : ∃ a : Fin r → ℝ, A = Matrix.vecMulVec a a := by
  classical
  obtain ⟨G, hG⟩ := hexagon_psd_gram_aux A hA
  have hGr : G.rank ≤ 1 := by
    rw [hG, Matrix.rank_conjTranspose_mul_self] at h; exact h
  rw [Matrix.rank, finrank_le_one_iff] at hGr
  obtain ⟨v, hv⟩ := hGr
  have hcol : ∀ l, ∃ c : ℝ, ∀ k, G k l = c * (v : Fin r → ℝ) k := by
    intro l
    obtain ⟨c, hc⟩ := hv ⟨fun i => G i l, ⟨Pi.single l 1, Matrix.mulVec_single_one G l⟩⟩
    refine ⟨c, fun k => ?_⟩
    have := congrArg (fun x : LinearMap.range G.mulVecLin => (x : Fin r → ℝ) k) hc
    simpa using this.symm
  choose c hc using hcol
  set S := ∑ k, (v : Fin r → ℝ) k ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  refine ⟨fun l => c l * Real.sqrt S, ?_⟩
  ext l l'
  rw [hG, Matrix.vecMulVec_apply, Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, star_trivial, hc]
  have : Real.sqrt S * Real.sqrt S = S := Real.mul_self_sqrt hS0
  have e : ∀ k, c l * (v : Fin r → ℝ) k * (c l' * (v : Fin r → ℝ) k) =
      (c l * c l') * (v : Fin r → ℝ) k ^ 2 := fun k => by ring
  simp only [e, ← Finset.mul_sum, ← hS]
  rw [show c l * Real.sqrt S * (c l' * Real.sqrt S) = c l * c l' * (Real.sqrt S * Real.sqrt S) by ring,
    this]

theorem trace_vecMulVec_mul_vecMulVec_self {r : ℕ} (a b : Fin r → ℝ) :
    (Matrix.vecMulVec a a * Matrix.vecMulVec b b).trace = (a ⬝ᵥ b) ^ 2 := by
  calc (Matrix.vecMulVec a a * Matrix.vecMulVec b b).trace
      = ∑ i, ∑ k, a i * a k * (b k * b i) := by
        simp [Matrix.trace, Matrix.mul_apply, Matrix.vecMulVec_apply]
    _ = (∑ i, a i * b i) * (∑ k, a k * b k) := by
        rw [Finset.sum_mul_sum]
        exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
    _ = (a ⬝ᵥ b) ^ 2 := by rw [sq]; rfl

theorem hexagon_slack_not_psd_factorization_le_three (r : ℕ) (hr : r ≤ 3) :
    ¬ matrix_has_psd_factorization
      (Matrix.of fun i j : Fin 6 => (((![0, 0, 1, 2, 2, 1] : Fin 6 → ℕ) (j - i) : ℕ) : ℝ)) r := by
  rintro ⟨A, B, hA, hB, hM⟩
  have z0 : ∀ i : Fin 6, (![0, 0, 1, 2, 2, 1] : Fin 6 → ℕ) (i - i) = 0 := by decide
  have z1 : ∀ i : Fin 6, (![0, 0, 1, 2, 2, 1] : Fin 6 → ℕ) ((i + 1) - i) = 0 := by decide
  have z2 : ∀ i : Fin 6, (![0, 0, 1, 2, 2, 1] : Fin 6 → ℕ) (i - (i - 1)) = 0 := by decide
  have xA : ∀ i : Fin 6, (![0, 0, 1, 2, 2, 1] : Fin 6 → ℕ) (i - (i + 1)) *
      (![0, 0, 1, 2, 2, 1] : Fin 6 → ℕ) ((i + 1) - (i + 2)) ≠
      (![0, 0, 1, 2, 2, 1] : Fin 6 → ℕ) ((i + 1) - (i + 1)) *
      (![0, 0, 1, 2, 2, 1] : Fin 6 → ℕ) (i - (i + 2)) := by decide
  have xB : ∀ j : Fin 6, (![0, 0, 1, 2, 2, 1] : Fin 6 → ℕ) ((j + 1) - (j - 1)) *
      (![0, 0, 1, 2, 2, 1] : Fin 6 → ℕ) ((j + 2) - j) ≠
      (![0, 0, 1, 2, 2, 1] : Fin 6 → ℕ) ((j + 1) - j) *
      (![0, 0, 1, 2, 2, 1] : Fin 6 → ℕ) ((j + 2) - (j - 1)) := by decide
  set c : Fin 6 → ℕ := ![0, 0, 1, 2, 2, 1] with hc
  set H : Matrix (Fin 6) (Fin 6) ℝ := Matrix.of fun i j : Fin 6 => ((c (j - i) : ℕ) : ℝ) with hH
  have hHv : ∀ i j, H i j = ((c (j - i) : ℕ) : ℝ) := fun i j => rfl
  have hrA : ∀ i, (A i).rank ≤ 1 := by
    intro i
    refine psd_factor_rank_le_one_of_cross hr H A B hA hB hM i i (i + 1) ?_ ?_ (i + 1) (i + 2) ?_
    · rw [hHv]; exact_mod_cast z0 i
    · rw [hHv]; exact_mod_cast z1 i
    · simp only [hHv]; exact_mod_cast xA i
  have hM' : ∀ j i, H.transpose j i = (B j * A i).trace := by
    intro j i; rw [Matrix.trace_mul_comm]; exact hM i j
  have hrB : ∀ j, (B j).rank ≤ 1 := by
    intro j
    refine psd_factor_rank_le_one_of_cross hr H.transpose B A hB hA hM' j (j - 1) j ?_ ?_
      (j + 1) (j + 2) ?_
    · rw [Matrix.transpose_apply, hHv]; exact_mod_cast z2 j
    · rw [Matrix.transpose_apply, hHv]; exact_mod_cast z0 j
    · simp only [Matrix.transpose_apply, hHv]; exact_mod_cast xB j
  choose a ha using fun i => psd_rank_le_one_eq_vecMulVec (A i) (hA i) (hrA i)
  choose b hb using fun j => psd_rank_le_one_eq_vecMulVec (B j) (hB j) (hrB j)
  set x : Fin 6 → Fin 6 → ℝ := fun i j => a i ⬝ᵥ b j with hx
  have hN : ∀ i j (k : ℕ), c (j - i) = k → x i j ^ 2 = k := by
    intro i j k hk
    have := hM i j
    rw [ha, hb, trace_vecMulVec_mul_vecMulVec_self, hHv, hk] at this
    exact this.symm
  have hZ : ∀ i j, c (j - i) = 0 → x i j = 0 := by
    intro i j hk
    have := hN i j 0 hk
    simpa using this
  let R : Fin 4 → Fin 6 := ![2, 3, 4, 5]
  let C : Fin 4 → Fin 6 := ![0, 3, 4, 5]
  let P : Matrix (Fin 4) (Fin r) ℝ := fun k l => a (R k) l
  let Q : Matrix (Fin r) (Fin 4) ℝ := fun l k => b (C k) l
  have hPQ : P * Q = Matrix.of fun k k' => x (R k) (C k') := by
    ext k k'
    rw [Matrix.mul_apply, Matrix.of_apply]
    rfl
  have hdet : (P * Q).det = 0 := by
    by_contra hd
    have hu : IsUnit (P * Q) := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hd)
    have h4 := Matrix.rank_of_isUnit _ hu
    have h5 := Matrix.rank_mul_le_left P Q
    have h6 := Matrix.rank_le_width P
    simp only [Fintype.card_fin] at h4 h6
    omega
  have hM4 : (Matrix.of fun k k' => x (R k) (C k')) =
      !![x 2 0, x 2 3, x 2 4, x 2 5; x 3 0, x 3 3, x 3 4, x 3 5;
        x 4 0, x 4 3, x 4 4, x 4 5; x 5 0, x 5 3, x 5 4, x 5 5] := by
    ext k k'
    fin_cases k <;> fin_cases k' <;> rfl
  rw [hPQ, hM4] at hdet
  have e23 := hZ 2 3 (by rw [hc]; decide)
  have e33 := hZ 3 3 (by rw [hc]; decide)
  have e34 := hZ 3 4 (by rw [hc]; decide)
  have e44 := hZ 4 4 (by rw [hc]; decide)
  have e45 := hZ 4 5 (by rw [hc]; decide)
  have e50 := hZ 5 0 (by rw [hc]; decide)
  have e55 := hZ 5 5 (by rw [hc]; decide)
  rw [e23, e33, e34, e44, e45, e50, e55] at hdet
  have s1 : Fin.succAbove (2 : Fin 4) (2 : Fin 3) = 3 := by decide
  have s2 : Fin.succAbove (3 : Fin 4) (2 : Fin 3) = 2 := by decide
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, s1, s2] at hdet
  have hp := hN 2 0 2 (by rw [hc]; decide)
  have hq := hN 2 4 1 (by rw [hc]; decide)
  have hs := hN 2 5 2 (by rw [hc]; decide)
  have ht := hN 3 0 2 (by rw [hc]; decide)
  have hu := hN 3 5 1 (by rw [hc]; decide)
  have hv := hN 4 0 1 (by rw [hc]; decide)
  have hw := hN 4 3 1 (by rw [hc]; decide)
  have hy := hN 5 3 2 (by rw [hc]; decide)
  have hz := hN 5 4 1 (by rw [hc]; decide)
  push_cast at hp hq hs ht hu hv hw hy hz
  have hD : x 2 0 * x 3 5 * x 4 3 * x 5 4 + x 2 4 * x 3 5 * x 4 0 * x 5 3 =
      x 2 5 * x 3 0 * x 4 3 * x 5 4 := by
    first | linear_combination hdet | linear_combination -hdet
  have e : (x 2 0 * x 3 5 * x 4 3 * x 5 4 + x 2 4 * x 3 5 * x 4 0 * x 5 3) ^ 2 -
      (x 2 5 * x 3 0 * x 4 3 * x 5 4) ^ 2 = 0 := by rw [hD]; ring
  have e2 : (x 2 0 * x 3 5 * x 4 3 * x 5 4 + x 2 4 * x 3 5 * x 4 0 * x 5 3) ^ 2 -
      (x 2 5 * x 3 0 * x 4 3 * x 5 4) ^ 2 =
      x 2 0 ^ 2 * x 3 5 ^ 2 * x 4 3 ^ 2 * x 5 4 ^ 2 + x 2 4 ^ 2 * x 3 5 ^ 2 * x 4 0 ^ 2 * x 5 3 ^ 2
      + 2 * (x 2 0 * x 2 4 * x 4 0 * x 4 3 * x 5 3 * x 5 4) * x 3 5 ^ 2
      - x 2 5 ^ 2 * x 3 0 ^ 2 * x 4 3 ^ 2 * x 5 4 ^ 2 := by ring
  rw [e2, hp, hq, hs, ht, hu, hv, hw, hy, hz] at e
  have h0 : x 2 0 * x 2 4 * x 4 0 * x 4 3 * x 5 3 * x 5 4 = 0 := by linarith
  have h1 : (x 2 0 * x 2 4 * x 4 0 * x 4 3 * x 5 3 * x 5 4) ^ 2 =
      x 2 0 ^ 2 * x 2 4 ^ 2 * x 4 0 ^ 2 * x 4 3 ^ 2 * x 5 3 ^ 2 * x 5 4 ^ 2 := by ring
  rw [h0, hp, hq, hv, hw, hy, hz] at h1
  norm_num at h1

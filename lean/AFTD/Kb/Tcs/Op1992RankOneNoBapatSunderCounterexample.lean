import AFTD.Prelude
import AFTD.Kb.Tcs.HasRealBapatSunderCounterexampleOfRank
import AFTD.Kb.Tcs.IsRealBapatSunderCounterexample
import AFTD.Kb.Tcs.MatrixPermanentSuccRow
import AFTD.Kb.Tcs.BapatSunderMatrix

/-!
# op_1992_rank_one_no_bapat_sunder_counterexample

Topic: combinatorics   Node: 2ee734b2a495

Provenance: formalization of a published result. Source: arXiv:2611.23269, Section 1 and Section 5

There does not exist a real positive semidefinite counterexample to the Bapat-Sunder eigenvalue conjecture of rank 1.
-/

open Matrix in
lemma op_1992_rank_one_cauchy_schwarz_ones {n : ℕ} (x : Fin (n + 1) → ℝ) :
    (∑ i, x i) ^ 2 ≤ (n + 1 : ℝ) * (x ⬝ᵥ x) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ => (1 : ℝ)) x
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, one_pow,
    one_mul, Nat.cast_add, Nat.cast_one] at h
  have hd : (∑ i, x i ^ 2) = x ⬝ᵥ x := by
    simp [dotProduct, sq]
  rw [hd] at h
  exact h

open Matrix in
lemma op_1992_rank_one_matrix_rank_one_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (h : A.rank = 1) :
    ∃ (u : Fin m → ℝ) (v : Fin n → ℝ), ∀ i j, A i j = u i * v j := by
  dsimp [Matrix.rank] at h
  have h_pos : 0 < Module.finrank ℝ A.mulVecLin.range := by omega
  have : Nontrivial A.mulVecLin.range := Module.nontrivial_of_finrank_pos h_pos
  obtain ⟨⟨w, hw⟩, hw0⟩ := exists_ne (0 : A.mulVecLin.range)
  have hw_ne : (⟨w, hw⟩ : A.mulVecLin.range) ≠ 0 := hw0
  have h_span := fun (y : A.mulVecLin.range) => exists_smul_eq_of_finrank_eq_one h hw_ne y
  choose c hc using fun (j : Fin n) =>
    h_span ⟨A.mulVecLin (Pi.single j 1), LinearMap.mem_range_self _ _⟩
  use w, c
  intro i j
  have hj := hc j
  apply_fun Subtype.val at hj
  change c j • w = A.mulVecLin (Pi.single j 1) at hj
  apply_fun (fun f => f i) at hj
  simp only [Pi.smul_apply, smul_eq_mul] at hj
  have h_col : A.mulVecLin (Pi.single j 1) i = A i j := by
    simp [mulVec, dotProduct, Pi.single_apply]
  rw [h_col] at hj
  rw [← hj, mul_comm]

open Matrix in
lemma op_1992_rank_one_permanent_rank_one {n : ℕ} {R : Type*} [CommRing R]
    (u v : Fin n → R) :
    (Matrix.of (fun i j => u i * v j)).permanent =
    (Nat.factorial n : R) * ((∏ i, u i) * (∏ j, v j)) := by
  unfold Matrix.permanent
  have hσ : ∀ σ : Equiv.Perm (Fin n), (∏ i, Matrix.of (fun i j => u i * v j) (σ i) i) = (∏ i, u i) * (∏ j, v j) := by
    intro σ
    simp only [of_apply, Finset.prod_mul_distrib]
    congr 1
    exact Equiv.prod_comp σ u
  have : (fun σ : Equiv.Perm (Fin n) => ∏ i, Matrix.of (fun i j => u i * v j) (σ i) i) =
         (fun _ => (∏ i, u i) * (∏ j, v j)) := funext hσ
  rw [this]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

open Matrix in
lemma op_1992_rank_one_bapat_sunder_matrix_rank_one {n : ℕ} (u v : Fin (n + 1) → ℝ)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : ∀ i j, A i j = u i * v j)
    (i j : Fin (n + 1)) :
    bapat_sunder_matrix A i j = (Nat.factorial n : ℝ) * (∏ k, u k) * (∏ k, v k) := by
  dsimp [bapat_sunder_matrix]
  rw [hA]
  have hsub : A.submatrix i.succAbove j.succAbove =
      Matrix.of (fun a b => (u ∘ i.succAbove) a * (v ∘ j.succAbove) b) := by
    ext a b
    simp [submatrix_apply, hA]
  rw [hsub, op_1992_rank_one_permanent_rank_one]
  have hu : u i * ∏ a, (u ∘ i.succAbove) a = ∏ k, u k := (Fin.prod_univ_succAbove u i).symm
  have hv : v j * ∏ b, (v ∘ j.succAbove) b = ∏ k, v k := (Fin.prod_univ_succAbove v j).symm
  calc
    u i * v j * ((Nat.factorial n : ℝ) * ((∏ a, (u ∘ i.succAbove) a) * (∏ b, (v ∘ j.succAbove) b)))
      = (Nat.factorial n : ℝ) * (u i * ∏ a, (u ∘ i.succAbove) a) * (v j * ∏ b, (v ∘ j.succAbove) b) := by ring
    _ = (Nat.factorial n : ℝ) * (∏ k, u k) * (∏ k, v k) := by rw [hu, hv]

open Matrix in
lemma op_1992_rank_one_posSemidef_diag_nonneg {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hA : A.PosSemidef) (k : Fin (n + 1)) : 0 ≤ A k k := by
  have h := hA.2 (Finsupp.single k (1 : ℝ))
  rw [Finsupp.sum_single_index] at h
  · rw [Finsupp.sum_single_index] at h
    · simp at h
      exact h
    · simp
  · simp

/-- No real positive semidefinite matrix of rank 1 is a Bapat-Sunder counterexample. -/
theorem op_1992_rank_one_no_bapat_sunder_counterexample :
    ¬ has_real_bapat_sunder_counterexample_of_rank 1 := by
  intro ⟨n, A, h_rank, h_psd, x, hx⟩
  obtain ⟨u, v, hA⟩ := op_1992_rank_one_matrix_rank_one_eq A h_rank
  set c := (Nat.factorial n : ℝ) * (∏ k, u k) * (∏ k, v k) with hc_def
  have hF : bapat_sunder_matrix A = Matrix.of (fun _ _ => c) := by
    ext i j
    simp only [Matrix.of_apply]
    exact op_1992_rank_one_bapat_sunder_matrix_rank_one u v A hA i j
  have h_prod : (∏ k, u k) * (∏ k, v k) = ∏ k, A k k := by
    rw [← Finset.prod_mul_distrib]
    congr 1
    ext k
    exact (hA k k).symm
  have hc_nonneg : 0 ≤ c := by
    rw [hc_def, mul_assoc, h_prod]
    have h1 : 0 ≤ (Nat.factorial n : ℝ) := Nat.cast_nonneg _
    have h2 : 0 ≤ ∏ k, A k k := Finset.prod_nonneg (fun k _ => op_1992_rank_one_posSemidef_diag_nonneg A h_psd k)
    exact mul_nonneg h1 h2
  have h_sum : ∑ j : Fin (n + 1), bapat_sunder_matrix A 0 j = A.permanent := by
    dsimp [bapat_sunder_matrix]
    exact (matrix_permanent_succ_row A 0).symm
  have h_per : (n + 1 : ℝ) * c = A.permanent := by
    rw [← h_sum]
    have : ∀ j : Fin (n + 1), bapat_sunder_matrix A 0 j = c := fun j => by
      rw [hF]; simp
    simp_rw [this]
    simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
  have h_quad : x ⬝ᵥ (bapat_sunder_matrix A).mulVec x = c * (∑ i, x i) ^ 2 := by
    rw [hF]
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, sq]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
    ring
  have h_cs : (∑ i, x i) ^ 2 ≤ (n + 1 : ℝ) * (x ⬝ᵥ x) := op_1992_rank_one_cauchy_schwarz_ones x
  have h_le : c * (∑ i, x i) ^ 2 ≤ A.permanent * (x ⬝ᵥ x) := by
    calc
      c * (∑ i, x i) ^ 2 ≤ c * ((n + 1 : ℝ) * (x ⬝ᵥ x)) := mul_le_mul_of_nonneg_left h_cs hc_nonneg
      _ = ((n + 1 : ℝ) * c) * (x ⬝ᵥ x) := by ring
      _ = A.permanent * (x ⬝ᵥ x) := by rw [h_per]
  linarith

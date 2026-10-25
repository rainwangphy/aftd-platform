import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixNuclearNorm
import AFTD.Kb.Tcs.MultisetMapUnivEqIff

/-!
# matrix_nuclear_norm_of_isHermitian

Topic: information   Node: e2d78ec33952

Provenance: formalization of a published result. Source: scout/2610-10618-the-hellinger-conjecture-for-antipodal-boolean-functions.md:315

For a real symmetric matrix $M$, its nuclear norm equals the sum of the absolute values of its eigenvalues.
-/

open Matrix Unitary Polynomial
open scoped BigOperators Matrix

lemma matrix_nuclear_norm_of_isHermitian_charpoly_sq {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (hM : M.IsHermitian) :
    (M * M).charpoly = ∏ i, (X - C ((hM.eigenvalues i)^2)) := by
  have h_sq : M * M = conjStarAlgAut ℝ _ hM.eigenvectorUnitary
      (diagonal (fun i => (hM.eigenvalues i)^2)) := by
    conv_lhs => rw [hM.spectral_theorem]
    rw [← map_mul]
    congr 1
    rw [diagonal_mul_diagonal]
    ext i j
    simp [pow_two]
  rw [h_sq]
  rw [conjStarAlgAut_apply, charpoly_mul_comm, ← mul_assoc]
  simp [charpoly_diagonal]

/-- For a real symmetric matrix, the nuclear norm equals the sum of the absolute values of its eigenvalues. -/
theorem matrix_nuclear_norm_of_isHermitian {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (hM : M.IsHermitian) :
    matrix_nuclear_norm M = ∑ j : Fin (Fintype.card n), |hM.eigenvalues₀ j| := by
  let A : Matrix n n ℂ := M.map Complex.ofReal
  let hH := isHermitian_mul_conjTranspose_self Aᴴ
  have hA : Aᴴ = A := by
    ext i j
    have : M j i = M i j := by
      have h := congr_fun (congr_fun hM i) j
      simpa [conjTranspose_apply] using h
    simp [A, conjTranspose_apply, this]
  have hH_mat : Aᴴ * Aᴴᴴ = (M * M).map Complex.ofRealHom := by
    rw [conjTranspose_conjTranspose, hA]
    ext i j
    simp [A, mul_apply]
  have h_char : (Aᴴ * Aᴴᴴ).charpoly = ∏ i, (X - C ((hM.eigenvalues i : ℂ)^2)) := by
    rw [hH_mat, charpoly_map (M * M) Complex.ofRealHom, matrix_nuclear_norm_of_isHermitian_charpoly_sq M hM]
    simp [Polynomial.map_prod]
  have h_ne_zero : (∏ i, (X - C ((hM.eigenvalues i : ℂ)^2))) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    exact X_sub_C_ne_zero _
  have h_roots_char : (Aᴴ * Aᴴᴴ).charpoly.roots =
      Multiset.map (fun i => ((hM.eigenvalues i : ℂ)^2)) Finset.univ.val := by
    rw [h_char, Polynomial.roots_prod _ _ h_ne_zero]
    simp [-map_pow]
  have h_roots_eig : (Aᴴ * Aᴴᴴ).charpoly.roots =
      Multiset.map (Complex.ofReal ∘ hH.eigenvalues) Finset.univ.val :=
    hH.roots_charpoly_eq_eigenvalues
  have h_map_eq : Multiset.map Complex.ofReal (Multiset.map hH.eigenvalues Finset.univ.val) =
      Multiset.map Complex.ofReal (Multiset.map (fun i => (hM.eigenvalues i)^2) Finset.univ.val) := by
    rw [Multiset.map_map, Multiset.map_map]
    rw [← h_roots_eig, h_roots_char]
    congr 1
    ext i
    exact (map_pow Complex.ofRealHom _ 2).symm
  have h_real_eq : Multiset.map hH.eigenvalues Finset.univ.val =
      Multiset.map (fun i => (hM.eigenvalues i)^2) Finset.univ.val :=
    Multiset.map_injective Complex.ofReal_injective h_map_eq
  rw [Multiset.map_univ_eq_iff] at h_real_eq
  obtain ⟨e, he⟩ := h_real_eq
  have h_sum_sqrt : ∑ i : n, Real.sqrt (hH.eigenvalues i) = ∑ i : n, |hM.eigenvalues i| := by
    have he_app (i : n) : hH.eigenvalues i = (hM.eigenvalues (e i))^2 := congr_fun he i
    simp_rw [he_app, Real.sqrt_sq_eq_abs]
    exact Equiv.sum_comp e (fun x => |hM.eigenvalues x|)
  have h_def : matrix_nuclear_norm M = ∑ i : n, Real.sqrt (hH.eigenvalues i) := rfl
  rw [h_def, h_sum_sqrt]
  change (∑ i : n, |hM.eigenvalues₀ ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm i)|) = _
  exact Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm (fun j => |hM.eigenvalues₀ j|)

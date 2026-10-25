import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixNuclearNorm
import AFTD.Kb.Tcs.MatrixEigenvalues0LeOfSubPosSemidef
import AFTD.Kb.Tcs.MatrixNuclearNormOfIsHermitian

/-!
# matrix_nuclear_norm_eigenvalue_inequality

Topic: information   Node: ee20a1c03fd0

Provenance: formalization of a published result. Source: arXiv:2610.10618 Lemma 2.2 -- The Hellinger Conjecture for Antipodal Boolean Functions

Let $n$ be a finite type with decidable equality. Let $A$ and $B$ be real symmetric matrices indexed by $n \times n$, with eigenvalues $a_j$ and $b_j$ in nonincreasing order. Then the sum over $j \in \mathrm{Fin}(|n|)$ of $|a_j - b_j|$ is at most the nuclear norm of $A - B$.
-/

lemma matrix_nuclear_norm_eigenvalue_inequality_max_sub_max_neg (x : ℝ) :
    max x 0 - max (-x) 0 = x := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [max_eq_right (le_of_lt h), max_eq_left (by linarith : (0:ℝ) ≤ -x)]; ring
  · rw [h]; simp
  · rw [max_eq_left (le_of_lt h), max_eq_right (by linarith : -x ≤ 0)]; ring

lemma matrix_nuclear_norm_eigenvalue_inequality_max_add_max_neg (x : ℝ) :
    max x 0 + max (-x) 0 = |x| := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [max_eq_right (le_of_lt h), max_eq_left (by linarith : (0:ℝ) ≤ -x), abs_of_neg h]; ring
  · rw [h]; simp
  · rw [max_eq_left (le_of_lt h), max_eq_right (by linarith : -x ≤ 0), abs_of_pos h]; ring

lemma matrix_nuclear_norm_eigenvalue_inequality_psd {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℝ) (v : n → ℝ) (hv : ∀ i, 0 ≤ v i) :
    (U * Matrix.diagonal v * star U).PosSemidef := by
  set s : n → ℝ := fun i => Real.sqrt (v i) with hs
  set M : Matrix n n ℝ := Matrix.diagonal s * star U with hM
  have hstarU : star (star U) = U := by simp
  have hstardiag : star (Matrix.diagonal s) = Matrix.diagonal s := by
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    simp
  have hss : (fun i => s i * s i) = v := by
    funext i
    simp only [hs]
    rw [← pow_two]
    exact Real.sq_sqrt (hv i)
  have hdiagsq : Matrix.diagonal v = Matrix.diagonal s * Matrix.diagonal s := by
    rw [← hss, Matrix.diagonal_mul_diagonal]
  have hPP : U * Matrix.diagonal v * star U = star M * M := by
    rw [hM, star_mul, hstarU, hstardiag, hdiagsq]
    noncomm_ring
  rw [hPP]
  exact Matrix.posSemidef_conjTranspose_mul_self M

lemma matrix_nuclear_norm_eigenvalue_inequality_trace {n : Type*} [Fintype n] [DecidableEq n]
    (U : Matrix n n ℝ) (v : n → ℝ) (hU : star U * U = 1) :
    (U * Matrix.diagonal v * star U).trace = ∑ i, v i := by
  rw [Matrix.trace_mul_cycle U (Matrix.diagonal v) (star U), hU, one_mul, Matrix.trace_diagonal]

lemma matrix_nuclear_norm_eigenvalue_inequality_sum {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℝ) (hH : H.IsHermitian) (f : ℝ → ℝ) :
    ∑ i : n, f (hH.eigenvalues i) = ∑ j : Fin (Fintype.card n), f (hH.eigenvalues₀ j) := by
  unfold Matrix.IsHermitian.eigenvalues
  exact Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    (fun j => f (hH.eigenvalues₀ j))

lemma matrix_nuclear_norm_eigenvalue_inequality_trace_eig {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    A.trace = ∑ j : Fin (Fintype.card n), hA.eigenvalues₀ j := by
  rw [Matrix.IsHermitian.trace_eq_sum_eigenvalues hA]
  exact matrix_nuclear_norm_eigenvalue_inequality_sum A hA id

lemma matrix_nuclear_norm_eigenvalue_inequality_decomp {n : Type*} [Fintype n] [DecidableEq n]
    (H : Matrix n n ℝ) (hH : H.IsHermitian) :
    H = (↑hH.eigenvectorUnitary : Matrix n n ℝ) *
          Matrix.diagonal (fun i => max (hH.eigenvalues i) 0) *
          star (↑hH.eigenvectorUnitary : Matrix n n ℝ)
      - (↑hH.eigenvectorUnitary : Matrix n n ℝ) *
          Matrix.diagonal (fun i => max (-(hH.eigenvalues i)) 0) *
          star (↑hH.eigenvectorUnitary : Matrix n n ℝ) := by
  have hspec := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  conv_lhs => rw [hspec]
  have hdiag : Matrix.diagonal (fun i => max (hH.eigenvalues i) 0) -
        Matrix.diagonal (fun i => max (-(hH.eigenvalues i)) 0) =
      Matrix.diagonal (hH.eigenvalues) := by
    rw [Matrix.diagonal_sub]
    congr 1
    funext i
    exact matrix_nuclear_norm_eigenvalue_inequality_max_sub_max_neg (hH.eigenvalues i)
  have hd : RCLike.ofReal ∘ hH.eigenvalues = hH.eigenvalues := by
    funext i; simp
  rw [hd, ← hdiag]
  noncomm_ring

/-- Nuclear-norm eigenvalue inequality: for real symmetric matrices with ordered eigenvalues, the sum of absolute differences between paired eigenvalues is bounded by the nuclear norm of their difference. -/
theorem matrix_nuclear_norm_eigenvalue_inequality {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∑ j : Fin (Fintype.card n), |hA.eigenvalues₀ j - hB.eigenvalues₀ j| ≤ matrix_nuclear_norm (A - B) := by
  classical
  set hH : (A - B).IsHermitian := hA.sub hB with hhH
  set U : Matrix n n ℝ := ↑hH.eigenvectorUnitary with hU
  set dp : n → ℝ := fun i => max (hH.eigenvalues i) 0 with hdp
  set dn : n → ℝ := fun i => max (-(hH.eigenvalues i)) 0 with hdn
  set P : Matrix n n ℝ := U * Matrix.diagonal dp * star U with hPdef
  set N : Matrix n n ℝ := U * Matrix.diagonal dn * star U with hNdef
  have hP : P.PosSemidef := matrix_nuclear_norm_eigenvalue_inequality_psd U dp (fun i => le_max_right _ _)
  have hN : N.PosSemidef := matrix_nuclear_norm_eigenvalue_inequality_psd U dn (fun i => le_max_right _ _)
  have hUun : star U * U = 1 := Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hdecomp : A - B = P - N := matrix_nuclear_norm_eigenvalue_inequality_decomp (A - B) hH
  set C : Matrix n n ℝ := B + P with hCdef
  have hC : C.IsHermitian := hB.add hP.isHermitian
  have hCAeq : C - A = N := by
    have h' : N = P - (A - B) := by rw [hdecomp]; abel
    rw [hCdef, h']; abel
  have hCBeq : C - B = P := by rw [hCdef]; abel
  have hCA : (C - A).PosSemidef := hCAeq ▸ hN
  have hCB : (C - B).PosSemidef := hCBeq ▸ hP
  have hle : ∀ j, |hA.eigenvalues₀ j - hB.eigenvalues₀ j| ≤
      (hC.eigenvalues₀ j - hA.eigenvalues₀ j) + (hC.eigenvalues₀ j - hB.eigenvalues₀ j) := by
    intro j
    have h1 := matrix_eigenvalues₀_le_of_sub_posSemidef A C hA hC hCA j
    have h2 := matrix_eigenvalues₀_le_of_sub_posSemidef B C hB hC hCB j
    rw [abs_le]
    constructor <;> linarith
  have hbound := Finset.sum_le_sum (s := Finset.univ)
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin (Fintype.card n)))) => hle j)
  have htrC : ∑ j : Fin (Fintype.card n), hC.eigenvalues₀ j = C.trace :=
    (matrix_nuclear_norm_eigenvalue_inequality_trace_eig C hC).symm
  have htrA : ∑ j : Fin (Fintype.card n), hA.eigenvalues₀ j = A.trace :=
    (matrix_nuclear_norm_eigenvalue_inequality_trace_eig A hA).symm
  have htrB : ∑ j : Fin (Fintype.card n), hB.eigenvalues₀ j = B.trace :=
    (matrix_nuclear_norm_eigenvalue_inequality_trace_eig B hB).symm
  have hsum : ∑ j : Fin (Fintype.card n),
      ((hC.eigenvalues₀ j - hA.eigenvalues₀ j) + (hC.eigenvalues₀ j - hB.eigenvalues₀ j))
      = P.trace + N.trace := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, htrC, htrA, htrB]
    have h1 : C.trace - B.trace = P.trace := by
      rw [hCdef, Matrix.trace_add]; ring
    have h2 : C.trace - A.trace = N.trace := by
      rw [← Matrix.trace_sub, hCAeq]
    rw [h1, h2]; ring
  have htrP : P.trace = ∑ i : n, dp i := matrix_nuclear_norm_eigenvalue_inequality_trace U dp hUun
  have htrN : N.trace = ∑ i : n, dn i := matrix_nuclear_norm_eigenvalue_inequality_trace U dn hUun
  have htot : P.trace + N.trace = matrix_nuclear_norm (A - B) := by
    rw [htrP, htrN, ← Finset.sum_add_distrib]
    have hpt : (∑ i : n, (dp i + dn i)) = ∑ i : n, |hH.eigenvalues i| := by
      congr 1
      funext i
      exact matrix_nuclear_norm_eigenvalue_inequality_max_add_max_neg (hH.eigenvalues i)
    rw [hpt, matrix_nuclear_norm_eigenvalue_inequality_sum (A - B) hH (fun x => |x|)]
    exact (matrix_nuclear_norm_of_isHermitian (A - B) hH).symm
  linarith

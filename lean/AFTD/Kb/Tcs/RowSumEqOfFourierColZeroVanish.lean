import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicMatrixFourier

/-!
# row_sum_eq_of_fourier_col_zero_vanish

Topic: combinatorics   Node: e10322201054

Provenance: helper lemma. step towards sharp_cyclic_graph_is_regular

If the cyclic 2D Fourier transform of M has vanishing entries at (m,0) for all m ≠ 0, then all row sums of M are equal.
-/

private lemma row_sum_eq_of_fourier_col_zero_vanish_fourier_eq (N : ℕ) [NeZero N]
    (M : Matrix (ZMod N) (ZMod N) ℂ) (m : ZMod N) :
    cyclic_matrix_fourier N M m 0 =
      (N : ℂ)⁻¹ * ∑ x : ZMod N, (∑ y : ZMod N, M x y) * (ZMod.stdAddChar (m * x))⁻¹ := by
  simp only [cyclic_matrix_fourier, Matrix.of_apply, one_div, zero_mul, add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y hy
  congr 1
  rw [show (ZMod.stdAddChar (m * x)) =
      Complex.exp (2 * ↑Real.pi * Complex.I * (↑(m * x).val : ℂ) / ↑N) from by
    rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]]
  rw [← Complex.exp_neg]
  congr 1
  ring_nf

private lemma row_sum_eq_of_fourier_col_zero_vanish_dft_eq (N : ℕ) [NeZero N]
    (r : ZMod N → ℂ) (m : ZMod N) :
    ZMod.dft r m = ∑ x : ZMod N, (ZMod.stdAddChar (m * x))⁻¹ * r x := by
  rw [ZMod.dft_apply]
  apply Finset.sum_congr rfl
  intro x hx
  rw [smul_eq_mul, ← AddChar.map_neg_eq_inv]
  congr 1
  ring_nf

/-- If the 0-th column of the cyclic Fourier transform of a matrix M vanishes away from m=0, then all row sums of M are equal (Fourier inversion implies the row-sum function is constant). -/
theorem row_sum_eq_of_fourier_col_zero_vanish (N : ℕ) [NeZero N]
    (M : Matrix (ZMod N) (ZMod N) ℂ)
    (hF : ∀ m : ZMod N, m ≠ 0 → cyclic_matrix_fourier N M m 0 = 0) (x : ZMod N) :
    ∑ y : ZMod N, M x y = ∑ y : ZMod N, M 0 y := by
  have hFr : ∀ m : ZMod N, m ≠ 0 → ZMod.dft (fun x => ∑ y : ZMod N, M x y) m = 0 := by
    intro m hm
    have h := hF m hm
    rw [row_sum_eq_of_fourier_col_zero_vanish_fourier_eq] at h
    rw [row_sum_eq_of_fourier_col_zero_vanish_dft_eq]
    rcases mul_eq_zero.mp h with h1 | h2
    · exact absurd h1 (inv_ne_zero (by exact_mod_cast NeZero.ne N))
    · simpa [mul_comm] using h2
  have key : ∀ y : ZMod N, (∑ z : ZMod N, M y z) =
      (N : ℂ)⁻¹ * ZMod.dft (fun x => ∑ y : ZMod N, M x y) 0 := by
    intro y
    change (fun x => ∑ z : ZMod N, M x z) y = _
    rw [← LinearEquiv.symm_apply_apply ZMod.dft (fun x => ∑ z : ZMod N, M x z)]
    rw [ZMod.invDFT_apply]
    rw [Finset.sum_eq_single 0]
    · simp
    · intro b _ hb; rw [hFr b hb, smul_zero]
    · intro h; exact absurd (Finset.mem_univ 0) h
  rw [key x, key 0]

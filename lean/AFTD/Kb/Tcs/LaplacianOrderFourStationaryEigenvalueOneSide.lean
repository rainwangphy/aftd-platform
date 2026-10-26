import AFTD.Prelude
import AFTD.Kb.Tcs.ComplexLaplacianSectorCost
import AFTD.Kb.Tcs.ComplexLaplacianSectorCostSelf
import AFTD.Kb.Tcs.ComplexCycleFourLaplacianSectorCostNonneg
import AFTD.Kb.Tcs.FourVertexBalancedCostNonneg

/-!
# laplacian_order_four_stationary_eigenvalue_one_side

Topic: graphs   Node: 5cf1254e8404

Provenance: helper lemma. Sector-bound formalization for IN-166; arXiv:math/0508176, Theorem 5.

For a real order-four matrix with zero row sums, nonpositive off-diagonal entries, and a strictly positive left null vector, every complex eigenvalue has nonnegative real part plus imaginary part.
-/

theorem laplacian_order_four_stationary_eigenvalue_one_side
    (L : Matrix (Fin 4) (Fin 4) ℝ) (π : Fin 4 → ℝ)
    (hπ : ∀ i, 0 < π i)
    (hr : ∀ i, ∑ j, L i j = 0)
    (ho : ∀ i j, i ≠ j → L i j ≤ 0)
    (hs : ∀ j, ∑ i, π i * L i j = 0)
    (v : Fin 4 → ℂ) (hv0 : v ≠ 0) (z : ℂ)
    (hv : (L.map (algebraMap ℝ ℂ)).mulVec v = z • v) :
    0 ≤ z.re + z.im := by
  let w : Fin 4 → Fin 4 → ℝ := fun i j => -π i * L i j
  have hw : ∀ i j, i ≠ j → 0 ≤ w i j := by
    intro i j hij
    exact mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (hπ i).le) (ho i j hij)
  have hb : ∀ i, ∑ j, w i j = ∑ j, w j i := by
    intro i
    change (∑ j, -π i * L i j) = ∑ j, -π j * L j i
    calc
      (∑ j, -π i * L i j) = -π i * ∑ j, L i j := (Finset.mul_sum _ _ _).symm
      _ = 0 := by rw [hr i, mul_zero]
      _ = -(∑ j, π j * L j i) := by rw [hs i, neg_zero]
      _ = ∑ j, -π j * L j i := by simp only [neg_mul, Finset.sum_neg_distrib]
  have hnn := four_vertex_balanced_cost_nonneg w (fun i j => complex_laplacian_sector_cost (v i) (v j)) hw hb
    (fun i => complex_laplacian_sector_cost_self (v i))
    (fun i j k l => complex_cycle_four_laplacian_sector_cost_nonneg (v i) (v j) (v k) (v l))
  have hrow : ∀ i, (∑ j, w i j * complex_laplacian_sector_cost (v i) (v j)) =
      (z.re + z.im) * (π i * ((v i).re ^ 2 + (v i).im ^ 2)) := by
    intro i
    have hre : (∑ j, L i j * (v j).re) = z.re * (v i).re - z.im * (v i).im := by
      simpa [Matrix.mulVec, dotProduct, Complex.mul_re] using
        congrArg Complex.re (congrFun hv i)
    have him : (∑ j, L i j * (v j).im) = z.re * (v i).im + z.im * (v i).re := by
      simpa [Matrix.mulVec, dotProduct, Complex.mul_im] using
        congrArg Complex.im (congrFun hv i)
    have hr0 := hr i
    simp [Fin.sum_univ_succ] at hre him hr0 ⊢
    dsimp [w, complex_laplacian_sector_cost] at hre him hr0 ⊢
    linear_combination -π i * ((v i).re ^ 2 + (v i).im ^ 2) * hr0 +
      π i * ((v i).re - (v i).im) * hre +
      π i * ((v i).re + (v i).im) * him
  simp_rw [hrow, ← Finset.mul_sum] at hnn
  have hn : ∀ i, 0 ≤ π i * ((v i).re ^ 2 + (v i).im ^ 2) := by
    intro i
    exact mul_nonneg (hπ i).le (add_nonneg (sq_nonneg _) (sq_nonneg _))
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv0 (funext h)
  have hn_i : 0 < (v i).re ^ 2 + (v i).im ^ 2 := by
    by_contra hh
    have hx : (v i).re = 0 := by nlinarith [sq_nonneg (v i).im]
    have hy : (v i).im = 0 := by nlinarith [sq_nonneg (v i).re]
    exact hi (Complex.ext hx hy)
  have hpos : 0 < ∑ i, π i * ((v i).re ^ 2 + (v i).im ^ 2) := by
    exact lt_of_lt_of_le (mul_pos (hπ i) hn_i)
      (Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ i))
  nlinarith only [hnn, hpos]

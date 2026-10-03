import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CubeTangentLe

/-!
# qa_pool_tsallis_three_aux

Topic: mechanism_design   Node: 309ec51f3dae

KKT sufficiency on the 3-simplex for sum x_k^3 - <x, V>: if 3 x_k^2 - V_k >= lam for all k with equality where x_k > 0, then x minimizes over the simplex.
-/

lemma qa_pool_tsallis_three_aux (V : Fin 3 → ℝ) (x : Fin 3 → ℝ) (lam : ℝ)
    (hx : x ∈ stdSimplex ℝ (Fin 3))
    (hkkt : ∀ k, lam ≤ 3 * x k ^ 2 - V k ∧ (0 < x k → 3 * x k ^ 2 - V k = lam)) :
    ∀ y ∈ stdSimplex ℝ (Fin 3),
      ∑ k, x k ^ 3 - ∑ k, x k * V k ≤ ∑ k, y k ^ 3 - ∑ k, y k * V k := by
  intro y ⟨hy0, hy1⟩
  obtain ⟨hx0, hx1⟩ := hx
  have hstep : ∀ k, x k ^ 3 - x k * V k + (3 * x k ^ 2 - V k) * (y k - x k) ≤ y k ^ 3 - y k * V k := by
    intro k; have := cube_tangent_le (hy0 k) (hx0 k); nlinarith
  have hlin : ∀ k, lam * (y k - x k) ≤ (3 * x k ^ 2 - V k) * (y k - x k) := by
    intro k
    obtain ⟨h1, h2⟩ := hkkt k
    rcases (hx0 k).lt_or_eq with hpos | hzero
    · rw [h2 hpos]
    · rw [← hzero] at h1 ⊢; simp only [sub_zero]; exact mul_le_mul_of_nonneg_right h1 (hy0 k)
  have hsum : ∑ k, lam * (y k - x k) = 0 := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, hy1, hx1]; ring
  have := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => (hlin k).trans (by linarith [hstep k] :
    (3 * x k ^ 2 - V k) * (y k - x k) ≤ (y k ^ 3 - y k * V k) - (x k ^ 3 - x k * V k)))
  rw [hsum, Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib] at this
  linarith

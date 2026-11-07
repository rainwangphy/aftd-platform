import AFTD.Prelude
import AFTD.Kb.Tcs.SpectralMooreSeidelSwitch
import AFTD.Kb.Tcs.SpectralMooreAdjQuadformLeAddSumSq
import AFTD.Kb.Tcs.SpectralMooreSecondEigenvalueLe

/-!
# spectral_moore_seidel_switch_adj_quadform_le

Topic: graphs   Node: 1be8978c7693

Provenance: helper lemma. arXiv:2611.00591 (A spectral Moore problem and the Yang-Koolen conjecture), Section 5, Lemma 5.1, inequality (12)

Let G be a k-regular finite simple graph on V with second largest adjacency eigenvalue at most θ and k ≤ θ + |V|/2. Then for every X : Set V, the Seidel switching F = spectral_moore_seidel_switch G X satisfies x ⬝ᵥ (F.adjMatrix ℝ *ᵥ x) ≤ θ * (x ⬝ᵥ x) for every x : V → ℝ with ∑ v, x v = 0.
-/

open Classical SimpleGraph Matrix in
theorem spectral_moore_seidel_switch_adj_quadform_le {V : Type*} [Fintype V]
    (G : SimpleGraph V) (X : Set V) (k : ℕ) (θ : ℝ) (hreg : G.IsRegularOfDegree k)
    (hθ : spectral_moore_second_eigenvalue_le G θ)
    (hk : (k : ℝ) ≤ θ + (Fintype.card V : ℝ) / 2) (x : V → ℝ) (hx : ∑ v, x v = 0) :
    x ⬝ᵥ ((spectral_moore_seidel_switch G X).adjMatrix ℝ *ᵥ x) ≤ θ * (x ⬝ᵥ x) := by
  set s : V → ℝ := fun v => if v ∈ X then 1 else -1 with hs
  have hs2 : ∀ v, s v * s v = 1 := by intro v; simp only [hs]; split_ifs <;> norm_num
  have hentry : ∀ u v, (spectral_moore_seidel_switch G X).adjMatrix ℝ u v =
      (1 - s u * s v) / 2 + s u * s v * G.adjMatrix ℝ u v := by
    intro u v
    by_cases huv : u = v
    · subst huv; simp [hs2]
    have hadj : (spectral_moore_seidel_switch G X).Adj u v ↔ (G.Adj u v ↔ (u ∈ X ↔ v ∈ X)) := by
      change u ≠ v ∧ _ ↔ _
      simp [huv]
    rw [adjMatrix_apply, adjMatrix_apply]
    simp only [hs]
    by_cases hu : u ∈ X <;> by_cases hv : v ∈ X <;> by_cases hG : G.Adj u v <;>
      simp [hu, hv, hG, hadj]
  set y : V → ℝ := fun v => s v * x v with hy
  have hq := spectral_moore_adj_quadform_le_add_sum_sq G k θ hreg hθ hk y
  have hyy : y ⬝ᵥ y = x ⬝ᵥ x := by
    simp only [dotProduct, hy]
    exact Finset.sum_congr rfl fun v _ => by
      calc s v * x v * (s v * x v) = (s v * s v) * (x v * x v) := by ring
        _ = x v * x v := by rw [hs2, one_mul]
  have e : x ⬝ᵥ ((spectral_moore_seidel_switch G X).adjMatrix ℝ *ᵥ x) =
      (∑ v, x v) ^ 2 / 2 - (∑ v, y v) ^ 2 / 2 + y ⬝ᵥ (G.adjMatrix ℝ *ᵥ y) := by
    have L : ∀ (M : Matrix V V ℝ) (w : V → ℝ),
        w ⬝ᵥ (M *ᵥ w) = ∑ u, ∑ v, w u * M u v * w v := by
      intro M w
      simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]
    have R : ∀ w : V → ℝ, (∑ v, w v) ^ 2 = ∑ u, ∑ v, w u * w v := by
      intro w; rw [sq, Finset.sum_mul_sum]
    rw [L, L, R, R, Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hentry]; simp only [hy]; ring
  rw [e, hx, ← hyy]
  nlinarith [sq_nonneg (∑ v, y v)]

import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsQaPool
import AFTD.Kb.GameTheoryEconomics.TsallisExpectedReward
import AFTD.Kb.GameTheoryEconomics.TsallisExposure

/-!
# qa_pool_tsallis_three_unique

Topic: mechanism_design   Node: 4661843e7e22

For the cubic Tsallis rule the QA pool of any forecasts and weights is unique.
-/

/-- The QA pool for the cubic Tsallis rule is unique. -/
theorem qa_pool_tsallis_three_unique {n m : ℕ} (ps : Fin m → Fin n → ℝ) (w : Fin m → ℝ)
    (x x' : Fin n → ℝ)
    (hx : is_qa_pool (tsallis_expected_reward 3) (tsallis_exposure 3) ps w x)
    (hx' : is_qa_pool (tsallis_expected_reward 3) (tsallis_exposure 3) ps w x') : x = x' := by
  obtain ⟨⟨hx0, hx1⟩, hxmin⟩ := hx
  obtain ⟨⟨hx'0, hx'1⟩, hx'min⟩ := hx'
  set V : Fin n → ℝ := fun k => ∑ i, w i * tsallis_exposure 3 (ps i) k
  have hm : (fun k => (x k + x' k) / 2) ∈ stdSimplex ℝ (Fin n) := by
    refine ⟨fun k => by have := hx0 k; have := hx'0 k; positivity, ?_⟩
    rw [← Finset.sum_div, Finset.sum_add_distrib, hx1, hx'1]; norm_num
  have h1 := hxmin _ hm
  have h2 := hx'min _ ⟨hx0, hx1⟩
  have h3 := hxmin _ ⟨hx'0, hx'1⟩
  unfold tsallis_expected_reward at h1 h2 h3
  -- the convexity gap of the cube at the midpoint
  have key : ∑ k, (3 / 8 : ℝ) * (x k + x' k) * (x k - x' k) ^ 2 ≤ 0 := by
    have e : ∀ k, (3 / 8 : ℝ) * (x k + x' k) * (x k - x' k) ^ 2 =
        (x k ^ 3 + x' k ^ 3) / 2 - ((x k + x' k) / 2) ^ 3 := by intro k; ring
    simp_rw [e]
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib]
    have lin : ∑ k, (x k + x' k) / 2 * V k = (∑ k, x k * V k + ∑ k, x' k * V k) / 2 := by
      rw [← Finset.sum_add_distrib, Finset.sum_div]; congr 1; ext k; ring
    simp only [V] at lin
    linarith
  have hterm : ∀ k ∈ Finset.univ, 0 ≤ (3 / 8 : ℝ) * (x k + x' k) * (x k - x' k) ^ 2 := by
    intro k _; have := hx0 k; have := hx'0 k; positivity
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp (le_antisymm key (Finset.sum_nonneg hterm))
  funext k
  have := hz k (Finset.mem_univ k)
  rcases mul_eq_zero.mp this with h | h
  · have := hx0 k; have := hx'0 k
    have : x k + x' k = 0 := by linarith
    linarith
  · nlinarith [pow_eq_zero_iff (n := 2) (two_ne_zero) |>.mp h]

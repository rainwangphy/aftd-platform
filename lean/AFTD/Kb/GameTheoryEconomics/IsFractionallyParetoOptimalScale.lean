import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsFractionallyParetoOptimal
import AFTD.Kb.GameTheoryEconomics.GoodsUtility
import AFTD.Kb.Tcs.G
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# is_fractionally_pareto_optimal_scale

Topic: fair_division   Node: 29bb7168ebd0

Provenance: helper lemma. step towards scaled_common_ratio_bivalued_efx_fpo_envyfreeable

Multiplying each agent's additive valuation vector by a positive scale c_i > 0 preserves and reflects fractional Pareto optimality.
-/

private theorem is_fractionally_pareto_optimal_scale_gu {m n : ℕ} (u : Fin n → Fin m → ℝ) (σ : Fin m → Fin n)
    (c : Fin n → ℝ) (i : Fin n) :
    goods_utility (fun i g => c i * u i g) σ i = c i * goods_utility u σ i := by
  simp [goods_utility, additive_valuation, Finset.mul_sum]

private theorem is_fractionally_pareto_optimal_scale_fs {m : ℕ} (u : Fin m → ℝ) (x : Fin m → ℝ) (c : ℝ) :
    ∑ g, (c * u g) * x g = c * ∑ g, u g * x g := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  ring

private theorem fpo_exist_scale {m n : ℕ} (u : Fin n → Fin m → ℝ) (σ : Fin m → Fin n)
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) :
    (∃ x : Fin n → Fin m → ℝ, (∀ i g, 0 ≤ x i g) ∧ (∀ g, ∑ i, x i g = 1) ∧
      (∀ i, goods_utility (fun i g => c i * u i g) σ i ≤ ∑ g, (c i * u i g) * x i g) ∧
      ∃ i, goods_utility (fun i g => c i * u i g) σ i < ∑ g, (c i * u i g) * x i g) ↔
    (∃ x : Fin n → Fin m → ℝ, (∀ i g, 0 ≤ x i g) ∧ (∀ g, ∑ i, x i g = 1) ∧
      (∀ i, goods_utility u σ i ≤ ∑ g, u i g * x i g) ∧
      ∃ i, goods_utility u σ i < ∑ g, u i g * x i g) := by
  constructor
  · rintro ⟨x, hx, hsum, hle, hlt⟩
    refine ⟨x, hx, hsum, ?_, ?_⟩
    · intro i
      have h := hle i
      rw [is_fractionally_pareto_optimal_scale_gu, is_fractionally_pareto_optimal_scale_fs] at h
      exact (mul_le_mul_iff_of_pos_left (hc i)).mp h
    · obtain ⟨i, hi⟩ := hlt
      refine ⟨i, ?_⟩
      rw [is_fractionally_pareto_optimal_scale_gu, is_fractionally_pareto_optimal_scale_fs] at hi
      exact (mul_lt_mul_iff_of_pos_left (hc i)).mp hi
  · rintro ⟨x, hx, hsum, hle, hlt⟩
    refine ⟨x, hx, hsum, ?_, ?_⟩
    · intro i
      rw [is_fractionally_pareto_optimal_scale_gu, is_fractionally_pareto_optimal_scale_fs]
      exact (mul_le_mul_iff_of_pos_left (hc i)).mpr (hle i)
    · obtain ⟨i, hi⟩ := hlt
      refine ⟨i, ?_⟩
      rw [is_fractionally_pareto_optimal_scale_gu, is_fractionally_pareto_optimal_scale_fs]
      exact (mul_lt_mul_iff_of_pos_left (hc i)).mpr hi

/-- Fractional Pareto optimality of an allocation is invariant under multiplying each agent's valuation vector by a positive constant. -/
theorem is_fractionally_pareto_optimal_scale {m n : ℕ} (u : Fin n → Fin m → ℝ) (σ : Fin m → Fin n)
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i) :
    is_fractionally_pareto_optimal (fun i g => c i * u i g) σ ↔
    is_fractionally_pareto_optimal u σ := by
  simp only [is_fractionally_pareto_optimal]
  exact not_congr (fpo_exist_scale u σ c hc)

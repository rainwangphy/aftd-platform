import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GoodsUtility
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.IsFractionallyParetoOptimal

/-!
# fpo_of_itemwise_weighted_max

Topic: fair_division   Node: 7266f4c7a7cd

Provenance: helper lemma. step towards scaled_common_ratio_bivalued_efx_fpo_envyfreeable

If an allocation σ assigns each item g to an agent maximizing w_i * u_i(g) for positive weights w, then σ is fractionally Pareto optimal for additive utilities u.
-/

/-- An allocation that maximizes a positive weighted sum of utilities itemwise is fractionally Pareto optimal. -/
theorem fpo_of_itemwise_weighted_max {m n : ℕ}
    (u : Fin n → Fin m → ℝ) (σ : Fin m → Fin n)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hmax : ∀ (g : Fin m) (j : Fin n), w j * u j g ≤ w (σ g) * u (σ g) g) :
    is_fractionally_pareto_optimal u σ := by
  rintro ⟨x, hxnn, hxsum, hge, hgt⟩
  have hstep2 : ∑ i, w i * goods_utility u σ i = ∑ g, w (σ g) * u (σ g) g := by
    have h2 : ∀ i, w i * goods_utility u σ i
        = ∑ g ∈ bundle_of σ i, w (σ g) * u (σ g) g := by
      intro i
      rw [goods_utility, additive_valuation, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g hg
      have hg' : σ g = i := by simpa [bundle_of] using hg
      rw [← hg']
    rw [show (∑ i, w i * goods_utility u σ i)
          = ∑ i, ∑ g ∈ bundle_of σ i, w (σ g) * u (σ g) g from by
          apply Finset.sum_congr rfl; intro i _; exact h2 i]
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (Fin m)) σ
          (fun g => w (σ g) * u (σ g) g)]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr
    · simp [bundle_of]
    · intro g _; rfl
  have hstep3 : ∑ i, w i * (∑ g, u i g * x i g) ≤ ∑ g, w (σ g) * u (σ g) g := by
    have h3 : ∀ i, w i * (∑ g, u i g * x i g) = ∑ g, w i * u i g * x i g := by
      intro i
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro g _
      ring
    rw [show (∑ i, w i * (∑ g, u i g * x i g)) = ∑ i, ∑ g, w i * u i g * x i g from by
          apply Finset.sum_congr rfl; intro i _; exact h3 i]
    rw [Finset.sum_comm]
    calc ∑ g, ∑ i, w i * u i g * x i g
        ≤ ∑ g, ∑ i, w (σ g) * u (σ g) g * x i g := by
          apply Finset.sum_le_sum
          intro g _
          apply Finset.sum_le_sum
          intro i _
          have h1 : w i * u i g ≤ w (σ g) * u (σ g) g := hmax g i
          have h2 : 0 ≤ x i g := hxnn i g
          nlinarith [h1, h2]
      _ = ∑ g, w (σ g) * u (σ g) g := by
          apply Finset.sum_congr rfl
          intro g _
          rw [← Finset.mul_sum, hxsum g, mul_one]
  have hstep1 : ∑ i, w i * goods_utility u σ i
      < ∑ i, w i * (∑ g, u i g * x i g) := by
    apply Finset.sum_lt_sum
    · intro i _
      exact mul_le_mul_of_nonneg_left (hge i) (le_of_lt (hw i))
    · obtain ⟨k, hk⟩ := hgt
      exact ⟨k, Finset.mem_univ k, mul_lt_mul_of_pos_left hk (hw k)⟩
  linarith

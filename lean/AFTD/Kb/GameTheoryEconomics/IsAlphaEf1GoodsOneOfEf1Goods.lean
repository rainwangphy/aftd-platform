import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEf1Goods
import AFTD.Kb.GameTheoryEconomics.IsAlphaEf1Goods
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# is_alpha_ef1_goods_one_of_ef1_goods

Topic: fair_division   Node: 8cf9fd6f334e

Provenance: helper lemma. step towards op561_ratio_gt_sqrt5

If an allocation is exactly EF1 (in the is_ef1_goods sense) for nonnegative additive valuations, then it is 1-EF1 in the is_alpha_ef1_goods sense.
-/

theorem is_alpha_ef1_goods_one_of_ef1_goods {m n : ℕ} (u : Fin n → Fin m → ℝ) (σ : Fin m → Fin n) (hpos : ∀ i g, 0 ≤ u i g) (h : is_ef1_goods u σ) : is_alpha_ef1_goods u 1 σ := by
  intro i j _ hjne
  rcases h i j with hle | ⟨g, hg, hgle⟩
  · obtain ⟨g0, hg0⟩ := hjne
    refine ⟨g0, hg0, ?_⟩
    rw [one_mul]
    have hsub : additive_valuation (u i) ((bundle_of σ j).erase g0) ≤ additive_valuation (u i) (bundle_of σ j) := by
      dsimp [additive_valuation]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx
        exact Finset.mem_of_mem_erase hx
      · intro x _ _
        exact hpos i x
    linarith
  · refine ⟨g, hg, ?_⟩
    rw [one_mul]
    exact hgle

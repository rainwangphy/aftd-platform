import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.HasOnlineAlphaEf1Algorithm
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.IsExactPrediction
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.IsAlphaEf1Goods
import AFTD.Kb.GameTheoryEconomics.IsOnlineAlgorithm

/-!
# op561_has_online_algorithm_mono

Topic: fair_division   Node: e660c32dd838

Provenance: original. Related work: arXiv:2610.34625 Sec. 2.1

If there exists an online algorithm guaranteeing a beta-EF1 allocation for n agents under exact frequency predictions, then for any alpha <= beta, there exists an online algorithm guaranteeing an alpha-EF1 allocation.
-/

/-- Monotonicity of online EF1 approximation: guaranteeing ratio β implies guaranteeing any smaller ratio α ≤ β. -/
theorem op561_has_online_algorithm_mono (n : ℕ) {α β : ℝ} (hαβ : α ≤ β)
    (h : has_online_alpha_ef1_algorithm n β) :
    has_online_alpha_ef1_algorithm n α := by
  obtain ⟨alg, halg, hgood⟩ := h
  unfold has_online_alpha_ef1_algorithm
  exact ⟨alg, halg, fun m v a_hat hv hpred i j hij hne => by
    obtain ⟨g, hg, hle⟩ := hgood m v a_hat hv hpred i j hij hne
    refine ⟨g, hg, le_trans (mul_le_mul_of_nonneg_right hαβ ?_) hle⟩
    exact Finset.sum_nonneg fun x hx => hv i x⟩

import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.HasOnlineSingleHighAlphaEfx
import AFTD.Kb.GameTheoryEconomics.IsAlphaEfxGoods
import AFTD.Kb.GameTheoryEconomics.IsSingleHighProfile
import AFTD.Kb.GameTheoryEconomics.IsSingleHighValuation
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.IsOnlineAllocator

/-!
# op819_has_online_single_high_alpha_mono

Topic: fair_division   Node: 1d4bfcec6027

Provenance: helper lemma. arXiv:2610.34625

If a deterministic online algorithm guarantees a beta-EFX allocation for n agents and m goods under single-high valuations with ratio R >= 0, then for any alpha <= beta, there exists a deterministic online algorithm guaranteeing an alpha-EFX allocation.
-/

/-- Monotonicity of online single-high alpha-EFX solvability in the approximation ratio alpha. -/
theorem op819_has_online_single_high_alpha_mono {n m : ℕ} {R α β : ℝ} (hR : 0 ≤ R) (hαβ : α ≤ β)
    (h : has_online_single_high_alpha_efx n m R β) :
    has_online_single_high_alpha_efx n m R α := by
  rcases h with ⟨alg, halg_online, halg_efx⟩
  refine ⟨alg, halg_online, fun v hv i j hij g hg => ?_⟩
  have h_nonneg : 0 ≤ additive_valuation (v i) ((bundle_of (alg v) j).erase g) := by
    dsimp [additive_valuation]
    apply Finset.sum_nonneg
    intro x _
    rcases hv i with ⟨g0, hg0, hrest⟩
    by_cases hx : x = g0
    · rw [hx, hg0]; exact hR
    · rw [hrest x hx]; linarith
  exact le_trans (mul_le_mul_of_nonneg_right hαβ h_nonneg) (halg_efx v hv i j hij g hg)

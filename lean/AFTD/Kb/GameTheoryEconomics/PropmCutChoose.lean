import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PropmEfxSplit

/-!
# propm_cut_choose

Topic: fair_division   Node: 697d81a0bbff

Cut and choose on one set of items: the cutter keeps K, the chooser gets the rest; the chooser gets at least half, and the cutter misses half by at most half of any item given to the chooser.
-/

/-- Cut and choose on one parallel class `T`: the cutter (valuation `vc ≥ 0`) keeps `K`, the chooser (valuation `vh`) gets `T \ K`. The chooser gets at least half of `T`, and the cutter misses half of `T` by at most half of any item given to the chooser. -/
lemma propm_cut_choose {m : ℕ} (T : Finset (Fin m)) (vc vh : Fin m → ℝ) (hvc : ∀ x, 0 ≤ vc x) :
    ∃ K ⊆ T, (∀ g ∈ T \ K, ∑ x ∈ T, vc x ≤ 2 * ∑ x ∈ K, vc x + vc g) ∧
      ∑ x ∈ T, vh x ≤ 2 * ∑ x ∈ T \ K, vh x := by
  classical
  obtain ⟨X, hXT, h1, h2⟩ := propm_efx_split T vc hvc
  have hX : ∀ w : Fin m → ℝ, ∑ x ∈ T \ X, w x = ∑ x ∈ T, w x - ∑ x ∈ X, w x := fun w => by
    rw [← Finset.sum_sdiff hXT]; ring
  by_cases hc : 2 * ∑ x ∈ X, vh x ≤ ∑ x ∈ T, vh x
  · exact ⟨X, hXT, fun g hg => by linarith [h2 g hg], by rw [hX]; linarith⟩
  · refine ⟨T \ X, Finset.sdiff_subset, fun g hg => ?_, ?_⟩
    · rw [Finset.sdiff_sdiff_eq_self hXT] at hg
      rw [hX]; linarith [h1 g hg]
    · rw [Finset.sdiff_sdiff_eq_self hXT]; linarith

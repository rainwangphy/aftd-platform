import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods

/-!
# efx_of_bundle_card_le_one

Topic: fair_division   Node: 45762a3923aa

Provenance: helper lemma. step towards efx_four_agents_additive_exists

An allocation where each agent receives at most one good is unconditionally EFX for any nonnegative additive valuations.
-/

/-- An allocation where each agent receives at most one good (e.g. an injective assignment of goods to agents) is unconditionally EFX for any nonnegative additive valuations. -/
theorem efx_of_bundle_card_le_one {m n : ℕ} (u : Fin n → Fin m → ℝ) (hu : ∀ i g, 0 ≤ u i g) (σ : Fin m → Fin n) (hinj : Function.Injective σ) : is_efx_goods u σ := by
  intro i j hij g hg
  have herase : (bundle_of σ j).erase g = ∅ := by
    ext x
    simp only [Finset.mem_erase, bundle_of, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    rintro ⟨hne, hx⟩
    have hg_eq : σ g = j := by
      simpa [bundle_of] using hg
    exact hne (hinj (hx.trans hg_eq.symm))
  rw [herase]
  dsimp [additive_valuation]
  exact Finset.sum_nonneg (fun x _ => hu i x)

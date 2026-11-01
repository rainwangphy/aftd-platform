import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuationEraseOfMem
import AFTD.Kb.GameTheoryEconomics.AdditiveValuationBundleLastCases
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# is_efx_goods_insert_of_unenvied_of_min

Topic: fair_division   Node: 3059189f7f6c

Provenance: helper lemma. Helper for efx_four_agents_additive_exists (OP-7), campaign session IN-404, 2026-11-01. Standard cycle elimination and ordered insertion, arXiv:1707.04769v3 Lemma 6.1 and Appendix B; no novelty claim.

Adding a good to an unenvied agent preserves EFX if every other agent values the new good no more than every old good in that recipient's bundle; all item values are nonnegative.
-/

open Function Finset

theorem is_efx_goods_insert_of_unenvied_of_min {m n : ℕ} (u : Fin n → Fin (m+1) → ℝ)
    (hu : ∀ i g, 0 ≤ u i g) (σ : Fin m → Fin n)
    (hσ : is_efx_goods (fun i g => u i g.castSucc) σ) (s : Fin n)
    (hs : ∀ i, additive_valuation (fun g => u i g.castSucc) (bundle_of σ s) ≤
      additive_valuation (fun g => u i g.castSucc) (bundle_of σ i))
    (hmin : ∀ i, i ≠ s → ∀ g ∈ bundle_of σ s, u i (Fin.last m) ≤ u i g.castSucc) :
    is_efx_goods u (Fin.lastCases s σ) := by
  intro i j hij g hg
  have hg' : Fin.lastCases s σ g = j := by simpa [bundle_of] using hg
  rw [additive_valuation_erase_of_mem _ _ _ hg, additive_valuation_bundle_last_cases, additive_valuation_bundle_last_cases]
  by_cases hjs : j = s
  · have his : i ≠ s := by simpa only [hjs] using hij
    rw [hjs, if_pos rfl, if_neg his.symm]
    rcases Fin.eq_castSucc_or_eq_last g with ⟨a, rfl⟩ | rfl
    · have ha : a ∈ bundle_of σ s := by simpa [bundle_of, hjs] using hg'
      have hm := hmin i his a ha
      have hh := hs i
      linarith
    · exact sub_le_iff_le_add.mpr (by linarith [hs i])
  · try simp only [if_neg (Ne.symm hjs)]
    rcases Fin.eq_castSucc_or_eq_last g with ⟨a, rfl⟩ | rfl
    · have ha : a ∈ bundle_of σ j := by simpa [bundle_of] using hg'
      have hh := hσ i j hij a ha
      rw [additive_valuation_erase_of_mem _ _ _ ha] at hh
      split_ifs <;> linarith [hu i (Fin.last m)]
    · simp only [Fin.lastCases_last] at hg'
      exact (hjs hg'.symm).elim

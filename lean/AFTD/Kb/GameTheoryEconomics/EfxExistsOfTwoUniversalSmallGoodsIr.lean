import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuationEraseOfMem
import AFTD.Kb.GameTheoryEconomics.BundleOfPermuteAgents
import AFTD.Kb.GameTheoryEconomics.IsEfxGoodsAllPairs
import AFTD.Kb.GameTheoryEconomics.AdditiveValuationBundleLastCases
import AFTD.Kb.GameTheoryEconomics.FiniteTwoBonusOrderedAssignment
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# efx_exists_of_two_universal_small_goods_ir

Topic: fair_division   Node: 0667eddc5862

Provenance: original. Related work: Structural helper for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01. The baseline is universally least-good insertion for a common individual ranking in arXiv:1707.04769v3 Appendix B. Here the two new goods need not have a common order. Web searches on 2026-11-01 for two smallest goods, ordered pairs, common pair order, and EFX completion found no matching result; arXiv:2504.03951 concerns n+2 goods and does not supply this arbitrary-old-allocation preservation statement. This does not settle unrestricted four-agent EFX.

Let m and n be natural numbers with n positive. There are m+2 goods with nonnegative real additive values for n agents. Each agent values each of the last two goods no more than every one of the first m goods, with no required order between the last two. Given any complete EFX allocation of the first m goods, there exists a complete EFX allocation of all m+2 goods in which every agent has at least her original utility and any two old goods originally allocated together are still allocated together, possibly to a different agent. EFX tests deletion of every good, including a zero-valued one.
-/

open Function Finset

theorem efx_exists_of_two_universal_small_goods_ir {m n : ℕ} (hn : 0 < n)
    (u : Fin n → Fin (m+2) → ℝ) (hu : ∀ i g, 0 ≤ u i g)
    (hsmall₀ : ∀ (i : Fin n) (g : Fin m), u i (Fin.last m).castSucc ≤ u i g.castSucc.castSucc)
    (hsmall₁ : ∀ (i : Fin n) (g : Fin m), u i (Fin.last (m+1)) ≤ u i g.castSucc.castSucc)
    (σ : Fin m → Fin n) (hσ : is_efx_goods (fun i g => u i g.castSucc.castSucc) σ) :
    ∃ τ : Fin (m+2) → Fin n, is_efx_goods u τ ∧
      (∀ i, additive_valuation (fun g : Fin m => u i g.castSucc.castSucc) (bundle_of σ i) ≤
        additive_valuation (u i) (bundle_of τ i)) ∧
      (∀ g h : Fin m, σ g = σ h → τ g.castSucc.castSucc = τ h.castSucc.castSucc) := by
  classical
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let w (i j : Fin n) := additive_valuation (fun g : Fin m => u i g.castSucc.castSucc) (bundle_of σ j)
  let a (i : Fin n) := u i (Fin.last m).castSucc
  let b (i : Fin n) := u i (Fin.last (m+1))
  obtain ⟨p, r, s, hI, hA, hB⟩ := finite_two_bonus_ordered_assignment w a b
    (fun i => hu i _) (fun i => hu i _)
  let τ₀ : Fin m → Fin n := fun g => p.symm (σ g)
  let τ₁ : Fin (m+1) → Fin n := Fin.lastCases r τ₀
  let τ : Fin (m+2) → Fin n := Fin.lastCases s τ₁
  have hval (i j : Fin n) : additive_valuation (u i) (bundle_of τ j) =
      w i (p j) + (if j = r then a i else 0) + (if j = s then b i else 0) := by
    dsimp [τ, τ₁, τ₀]
    rw [additive_valuation_bundle_last_cases, additive_valuation_bundle_last_cases, bundle_of_permute_agents]
    simp only [w, a, b, eq_comm]
  have hown (i : Fin n) : w i i ≤ additive_valuation (u i) (bundle_of τ i) := by
    simpa only [hval] using hI i
  have htrim₀ (i : Fin n) (hi : i ≠ r) :
      additive_valuation (u i) (bundle_of τ r) - a i ≤
        additive_valuation (u i) (bundle_of τ i) := by
    have hh := hA i hi
    rw [hval, hval]
    simp only [ite_true]
    linarith
  have htrim₁ (i : Fin n) (hi : i ≠ s) :
      additive_valuation (u i) (bundle_of τ s) - b i ≤
        additive_valuation (u i) (bundle_of τ i) := by
    have hh := hB i hi
    rw [hval, hval]
    simp only [ite_true]
    linarith
  refine ⟨τ, ?_, ?_, ?_⟩
  · intro i j hij g hg
    have hg' : τ g = j := by simpa [bundle_of] using hg
    rw [additive_valuation_erase_of_mem _ _ _ hg]
    rcases Fin.eq_castSucc_or_eq_last g with ⟨g₁, rfl⟩ | rfl
    · rcases Fin.eq_castSucc_or_eq_last g₁ with ⟨g₀, rfl⟩ | rfl
      · by_cases hjr : j = r
        · have hi : i ≠ r := by simpa only [hjr] using hij
          rw [hjr]
          have hh := htrim₀ i hi
          have hl := hsmall₀ i g₀
          change a i ≤ u i g₀.castSucc.castSucc at hl
          linarith
        · by_cases hjs : j = s
          · have hi : i ≠ s := by simpa only [hjs] using hij
            rw [hjs]
            have hh := htrim₁ i hi
            have hl := hsmall₁ i g₀
            change b i ≤ u i g₀.castSucc.castSucc at hl
            linarith
          · have hold : g₀ ∈ bundle_of σ (p j) := by
              simpa [τ, τ₁, τ₀, bundle_of, Equiv.symm_apply_eq] using hg'
            have hh := is_efx_goods_all_pairs (fun i (g : Fin m) => u i g.castSucc.castSucc)
              (fun i g => hu i _) σ hσ i (p j) g₀ hold
            rw [additive_valuation_erase_of_mem _ _ _ hold] at hh
            change w i (p j) - u i g₀.castSucc.castSucc ≤ w i i at hh
            rw [hval]
            simp only [if_neg hjr, if_neg hjs, add_zero]
            exact hh.trans (hown i)
      · have howner : r = j := by simpa [τ, τ₁, τ₀] using hg'
        have hi : i ≠ r := by simpa only [← howner] using hij
        rw [← howner]
        exact htrim₀ i hi
    · have howner : s = j := by simpa [τ] using hg'
      have hi : i ≠ s := by simpa only [← howner] using hij
      rw [← howner]
      exact htrim₁ i hi
  
  · intro i
    exact hown i
  · intro g h hgh
    simp [τ, τ₁, τ₀, hgh]

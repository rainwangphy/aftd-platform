import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxThreeBonusDistinctNoNat
import AFTD.Kb.GameTheoryEconomics.EfxThreeBonusDistinctFeasibleNat
import AFTD.Kb.GameTheoryEconomics.EfxThreeBonusDistinctValues
import AFTD.Kb.GameTheoryEconomics.IsEfxGoodsNatCastIff
import AFTD.Kb.GameTheoryEconomics.AdditiveValuationBundleSumIte
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# efx_three_bonus_distinct_no_real

Topic: fair_division   Node: 2bd1b3835b65

Provenance: helper lemma. Finite obstruction to the distinct-recipient exchange route for OP-7, experiments 11403, 11405 and 11406.

For the explicit positive four-agent seven-good instance, if an EFX allocation assigns its four old goods to distinct agents and its three bonuses to distinct agents, some agent has utility less than her old utility 38.
-/

theorem efx_three_bonus_distinct_no_real (σ : Fin 7 → Fin 4)
    (hold : ∀ (a b : Fin 4), a ≠ b → σ (Fin.castAdd 3 a) ≠ σ (Fin.castAdd 3 b))
    (hbonus : ∀ (a b : Fin 3), a ≠ b → σ (Fin.natAdd 4 a) ≠ σ (Fin.natAdd 4 b))
    (hefx : is_efx_goods (fun i g => (efx_three_bonus_distinct_values i g : ℝ)) σ) :
    ∃ i : Fin 4, additive_valuation (fun g => (efx_three_bonus_distinct_values i g : ℝ)) (bundle_of σ i) < 38 := by
  classical
  by_contra h
  push Not at h
  apply efx_three_bonus_distinct_no_nat σ
  refine ⟨hold, hbonus, ?_, ?_⟩
  · intro i
    have hi := h i
    rw [additive_valuation_bundle_sum_ite] at hi
    have hcast :
        (∑ g, if σ g = i then (efx_three_bonus_distinct_values i g : ℝ) else 0)
          = ((∑ g, if σ g = i then efx_three_bonus_distinct_values i g else 0 : ℕ) : ℝ) := by
      push_cast
      rfl
    rw [hcast] at hi
    exact_mod_cast hi
  · intro i j hij g hg
    have hh := (is_efx_goods_nat_cast_iff efx_three_bonus_distinct_values σ).mp hefx
    have hm : g ∈ bundle_of σ j := by simpa [bundle_of] using hg
    have := hh i j hij g hm
    simpa only [bundle_of, Finset.sum_filter] using this

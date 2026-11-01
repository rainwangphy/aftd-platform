import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionFeasibleNat
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionValues
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionThreshold
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionCoarse

/-!
# efx_three_small_goods_obstruction_no_two_nat

Topic: fair_division   Node: b8c3fb976b83

Provenance: helper lemma. Route obstruction for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01. Experiments 11265, 11268, and 11269. The last independently exhausts all 16384 full coarse assignments and all 1152 old-permutation two-bonus states; a row scaling removes a welfare-maximizer tie. General Pareto-monotone EFX completion barriers are already known in arXiv:2002.05119v3 Section 5. This explicit three-universally-small-goods example constrains maximum-sum two-bonus completion, not EFX existence or the original-diagonal three-bonus conjecture, and carries no research-level novelty claim.

Every coarse allocation whose first old pair is given to agent 2 fails the conjunction of current utility preservation and the exact natural-number EFX inequalities in the explicit eleven-good instance.
-/

open Function Finset

private lemma efx_three_small_goods_obstruction_no_two_nat_sum_id (p : Fin 7 → Fin 4) (i : Fin 4) :
  (∑ h : Fin 11, if efx_three_small_goods_obstruction_coarse p h = i then efx_three_small_goods_obstruction_values i h else 0)
  = (if p 0 = i then efx_three_small_goods_obstruction_values i 0 + efx_three_small_goods_obstruction_values i 1 else 0)
    + (if p 1 = i then efx_three_small_goods_obstruction_values i 2 + efx_three_small_goods_obstruction_values i 3 else 0)
    + (if p 2 = i then efx_three_small_goods_obstruction_values i 4 + efx_three_small_goods_obstruction_values i 5 else 0)
    + (if p 3 = i then efx_three_small_goods_obstruction_values i 6 + efx_three_small_goods_obstruction_values i 7 else 0)
    + (if p 4 = i then efx_three_small_goods_obstruction_values i 8 else 0)
    + (if p 5 = i then efx_three_small_goods_obstruction_values i 9 else 0)
    + (if p 6 = i then efx_three_small_goods_obstruction_values i 10 else 0) := by
  simp only [efx_three_small_goods_obstruction_coarse, Fin.sum_univ_succ]
  by_cases h0 : p 0 = i <;> by_cases h1 : p 1 = i <;> by_cases h2 : p 2 = i <;>
    by_cases h3 : p 3 = i <;> by_cases h4 : p 4 = i <;> by_cases h5 : p 5 = i <;>
    by_cases h6 : p 6 = i <;> simp_all <;> omega

private lemma efx_three_small_goods_obstruction_no_two_nat_bound0 (e f g : Fin 4) :
    (if e = 0 then 83 else 0) + (if f = 0 then 115 else 0) + (if g = 0 then 2 else 0) ≤ 200 := by
  split_ifs <;> omega

private lemma efx_three_small_goods_obstruction_no_two_nat_bound1 (e f g : Fin 4) :
    (if e = 1 then 4 else 0) + (if f = 1 then 392 else 0) + (if g = 1 then 4 else 0) ≤ 400 := by
  split_ifs <;> omega

private lemma efx_three_small_goods_obstruction_no_two_nat_bound2 (e f g : Fin 4) :
    (if e = 2 then 34 else 0) + (if f = 2 then 2 else 0) + (if g = 2 then 164 else 0) ≤ 200 := by
  split_ifs <;> omega

private lemma efx_three_small_goods_obstruction_no_two_nat_bound3 (e f g : Fin 4) :
    (if e = 3 then 2 else 0) + (if f = 3 then 83 else 0) + (if g = 3 then 115 else 0) ≤ 200 := by
  split_ifs <;> omega

theorem efx_three_small_goods_obstruction_no_two_nat : ∀ b c d e f g : Fin 4,
    ¬ efx_three_small_goods_obstruction_feasible_nat ![2,b,c,d,e,f,g] := by
  intro b c d e f g hf
  have h0 := hf.1 0
  have h1 := hf.1 1
  have h2 := hf.1 2
  have h3 := hf.1 3
  rw [efx_three_small_goods_obstruction_no_two_nat_sum_id] at h0 h1 h2 h3
  simp [efx_three_small_goods_obstruction_values, efx_three_small_goods_obstruction_threshold] at h0 h1 h2 h3
  have hb0 := efx_three_small_goods_obstruction_no_two_nat_bound0 e f g
  have hb1 := efx_three_small_goods_obstruction_no_two_nat_bound1 e f g
  have hb2 := efx_three_small_goods_obstruction_no_two_nat_bound2 e f g
  have hb3 := efx_three_small_goods_obstruction_no_two_nat_bound3 e f g
  fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp at h0 h1 h2 h3 <;> omega

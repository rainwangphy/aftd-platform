import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionFeasibleNat
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionCoarse
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionValues
import AFTD.Kb.GameTheoryEconomics.EfxThreeSmallGoodsObstructionThreshold
import AFTD.Kb.Tcs.G

/-!
# efx_three_small_goods_obstruction_no_one_nat

Topic: fair_division   Node: 3deccaf505e5

Provenance: helper lemma. Route obstruction for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01. Experiments 11265, 11268, and 11269. The last independently exhausts all 16384 full coarse assignments and all 1152 old-permutation two-bonus states; a row scaling removes a welfare-maximizer tie. General Pareto-monotone EFX completion barriers are already known in arXiv:2002.05119v3 Section 5. This explicit three-universally-small-goods example constrains maximum-sum two-bonus completion, not EFX existence or the original-diagonal three-bonus conjecture, and carries no research-level novelty claim.

Every coarse allocation whose first old pair is given to agent 1 fails the conjunction of current utility preservation and the exact natural-number EFX inequalities in the explicit eleven-good instance.
-/

open Function Finset

private lemma efx_three_small_goods_obstruction_no_one_nat_chunk_0_0 :
    ∀ d e f g : Fin 4,
      ¬ (∀ (i : Fin 4),
          efx_three_small_goods_obstruction_threshold i ≤
            ∑ h, if efx_three_small_goods_obstruction_coarse ![1, (0:Fin 4), (0:Fin 4), d, e, f, g] h = i
                 then efx_three_small_goods_obstruction_values i h else 0) := by
  decide

private lemma efx_three_small_goods_obstruction_no_one_nat_chunk_0_1 :
    ∀ d e f g : Fin 4,
      ¬ (∀ (i : Fin 4),
          efx_three_small_goods_obstruction_threshold i ≤
            ∑ h, if efx_three_small_goods_obstruction_coarse ![1, (0:Fin 4), (1:Fin 4), d, e, f, g] h = i
                 then efx_three_small_goods_obstruction_values i h else 0) := by
  decide

private lemma efx_three_small_goods_obstruction_no_one_nat_chunk_0_2 :
    ∀ d e f g : Fin 4,
      ¬ (∀ (i : Fin 4),
          efx_three_small_goods_obstruction_threshold i ≤
            ∑ h, if efx_three_small_goods_obstruction_coarse ![1, (0:Fin 4), (2:Fin 4), d, e, f, g] h = i
                 then efx_three_small_goods_obstruction_values i h else 0) := by
  decide

private lemma efx_three_small_goods_obstruction_no_one_nat_chunk_0_3 :
    ∀ d e f g : Fin 4,
      ¬ (∀ (i : Fin 4),
          efx_three_small_goods_obstruction_threshold i ≤
            ∑ h, if efx_three_small_goods_obstruction_coarse ![1, (0:Fin 4), (3:Fin 4), d, e, f, g] h = i
                 then efx_three_small_goods_obstruction_values i h else 0) := by
  decide

private lemma efx_three_small_goods_obstruction_no_one_nat_chunk_1_0 :
    ∀ d e f g : Fin 4,
      ¬ (∀ (i : Fin 4),
          efx_three_small_goods_obstruction_threshold i ≤
            ∑ h, if efx_three_small_goods_obstruction_coarse ![1, (1:Fin 4), (0:Fin 4), d, e, f, g] h = i
                 then efx_three_small_goods_obstruction_values i h else 0) := by
  decide

private lemma efx_three_small_goods_obstruction_no_one_nat_chunk_1_1 :
    ∀ d e f g : Fin 4,
      ¬ (∀ (i : Fin 4),
          efx_three_small_goods_obstruction_threshold i ≤
            ∑ h, if efx_three_small_goods_obstruction_coarse ![1, (1:Fin 4), (1:Fin 4), d, e, f, g] h = i
                 then efx_three_small_goods_obstruction_values i h else 0) := by
  decide

private lemma efx_three_small_goods_obstruction_no_one_nat_chunk_1_2 :
    ∀ d e f g : Fin 4,
      ¬ (∀ (i : Fin 4),
          efx_three_small_goods_obstruction_threshold i ≤
            ∑ h, if efx_three_small_goods_obstruction_coarse ![1, (1:Fin 4), (2:Fin 4), d, e, f, g] h = i
                 then efx_three_small_goods_obstruction_values i h else 0) := by
  decide

private lemma efx_three_small_goods_obstruction_no_one_nat_chunk_1_3 :
    ∀ d e f g : Fin 4,
      ¬ (∀ (i : Fin 4),
          efx_three_small_goods_obstruction_threshold i ≤
            ∑ h, if efx_three_small_goods_obstruction_coarse ![1, (1:Fin 4), (3:Fin 4), d, e, f, g] h = i
                 then efx_three_small_goods_obstruction_values i h else 0) := by
  decide

private lemma efx_three_small_goods_obstruction_no_one_nat_chunk_2_0 :
    ∀ d e f g : Fin 4,
      ¬ (∀ (i : Fin 4),
          efx_three_small_goods_obstruction_threshold i ≤
            ∑ h, if efx_three_small_goods_obstruction_coarse ![1, (2:Fin 4), (0:Fin 4), d, e, f, g] h = i
                 then efx_three_small_goods_obstruction_values i h else 0) := by
  decide

private lemma efx_three_small_goods_obstruction_no_one_nat_chunk_2_1 :
    ∀ d e f g : Fin 4,
      ¬ (∀ (i : Fin 4),
          efx_three_small_goods_obstruction_threshold i ≤
            ∑ h, if efx_three_small_goods_obstruction_coarse ![1, (2:Fin 4), (1:Fin 4), d, e, f, g] h = i
                 then efx_three_small_goods_obstruction_values i h else 0) := by
  decide

private lemma efx_three_small_goods_obstruction_no_one_nat_chunk_2_2 :
    ∀ d e f g : Fin 4,
      ¬ (∀ (i : Fin 4),
          efx_three_small_goods_obstruction_threshold i ≤
            ∑ h, if efx_three_small_goods_obstruction_coarse ![1, (2:Fin 4), (2:Fin 4), d, e, f, g] h = i
                 then efx_three_small_goods_obstruction_values i h else 0) := by
  decide

private lemma efx_three_small_goods_obstruction_no_one_nat_chunk_2_3 :
    ∀ d e f g : Fin 4,
      ¬ (∀ (i : Fin 4),
          efx_three_small_goods_obstruction_threshold i ≤
            ∑ h, if efx_three_small_goods_obstruction_coarse ![1, (2:Fin 4), (3:Fin 4), d, e, f, g] h = i
                 then efx_three_small_goods_obstruction_values i h else 0) := by
  decide

private lemma efx_three_small_goods_obstruction_no_one_nat_chunk_3_0 :
    ∀ d e f g : Fin 4,
      ¬ (∀ (i : Fin 4),
          efx_three_small_goods_obstruction_threshold i ≤
            ∑ h, if efx_three_small_goods_obstruction_coarse ![1, (3:Fin 4), (0:Fin 4), d, e, f, g] h = i
                 then efx_three_small_goods_obstruction_values i h else 0) := by
  decide

private lemma efx_three_small_goods_obstruction_no_one_nat_chunk_3_1 :
    ∀ d e f g : Fin 4,
      ¬ (∀ (i : Fin 4),
          efx_three_small_goods_obstruction_threshold i ≤
            ∑ h, if efx_three_small_goods_obstruction_coarse ![1, (3:Fin 4), (1:Fin 4), d, e, f, g] h = i
                 then efx_three_small_goods_obstruction_values i h else 0) := by
  decide

private lemma efx_three_small_goods_obstruction_no_one_nat_chunk_3_2 :
    ∀ d e f g : Fin 4,
      ¬ (∀ (i : Fin 4),
          efx_three_small_goods_obstruction_threshold i ≤
            ∑ h, if efx_three_small_goods_obstruction_coarse ![1, (3:Fin 4), (2:Fin 4), d, e, f, g] h = i
                 then efx_three_small_goods_obstruction_values i h else 0) := by
  decide

private lemma efx_three_small_goods_obstruction_no_one_nat_chunk_3_3 :
    ∀ d e f g : Fin 4,
      ¬ (∀ (i : Fin 4),
          efx_three_small_goods_obstruction_threshold i ≤
            ∑ h, if efx_three_small_goods_obstruction_coarse ![1, (3:Fin 4), (3:Fin 4), d, e, f, g] h = i
                 then efx_three_small_goods_obstruction_values i h else 0) := by
  decide

theorem efx_three_small_goods_obstruction_no_one_nat : ∀ b c d e f g : Fin 4,
    ¬ efx_three_small_goods_obstruction_feasible_nat ![1,b,c,d,e,f,g] := by
  intro b c d e f g h
  have h1 := h.1
  fin_cases b <;> fin_cases c
  · exact efx_three_small_goods_obstruction_no_one_nat_chunk_0_0 d e f g h1
  · exact efx_three_small_goods_obstruction_no_one_nat_chunk_0_1 d e f g h1
  · exact efx_three_small_goods_obstruction_no_one_nat_chunk_0_2 d e f g h1
  · exact efx_three_small_goods_obstruction_no_one_nat_chunk_0_3 d e f g h1
  · exact efx_three_small_goods_obstruction_no_one_nat_chunk_1_0 d e f g h1
  · exact efx_three_small_goods_obstruction_no_one_nat_chunk_1_1 d e f g h1
  · exact efx_three_small_goods_obstruction_no_one_nat_chunk_1_2 d e f g h1
  · exact efx_three_small_goods_obstruction_no_one_nat_chunk_1_3 d e f g h1
  · exact efx_three_small_goods_obstruction_no_one_nat_chunk_2_0 d e f g h1
  · exact efx_three_small_goods_obstruction_no_one_nat_chunk_2_1 d e f g h1
  · exact efx_three_small_goods_obstruction_no_one_nat_chunk_2_2 d e f g h1
  · exact efx_three_small_goods_obstruction_no_one_nat_chunk_2_3 d e f g h1
  · exact efx_three_small_goods_obstruction_no_one_nat_chunk_3_0 d e f g h1
  · exact efx_three_small_goods_obstruction_no_one_nat_chunk_3_1 d e f g h1
  · exact efx_three_small_goods_obstruction_no_one_nat_chunk_3_2 d e f g h1
  · exact efx_three_small_goods_obstruction_no_one_nat_chunk_3_3 d e f g h1

import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleIsAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCutAndChooseAlloc
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCutAndChooseAllocOne
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCutAndChooseAllocZero
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique

/-!
# SocialChoice.FairDivision.Divisible.cutAndChooseAlloc_isAllocation

Topic: fair_division   Node: 41e6a4251feb

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.cutAndChooseAlloc_isAllocation`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/CutAndChoose.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For any cut point `t`, the cut-and-choose allocation is a complete measurable partition of `[0,1]` into two pieces. This holds regardless of whether the cut is fair.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped unitInterval in
/-- For any cut point `t`, the cut-and-choose allocation is a complete measurable partition of `[0,1]` into two pieces. This holds regardless of whether the cut is fair. -/
theorem SocialChoice.FairDivision.Divisible.cutAndChooseAlloc_isAllocation (μ : Fin 2 → Measure I) (t : I) :
    IsAllocation (cutAndChooseAlloc μ t) := by
  have hmL  : MeasurableSet (Iic t : Set I)    := measurableSet_Iic
  have hmR  : MeasurableSet (Ioi t : Set I)    := measurableSet_Ioi
  have hdLR : Disjoint (Iic t : Set I) (Ioi t) := Iic_disjoint_Ioi le_rfl
  have hcov : (Iic t : Set I) ∪ Ioi t = univ   := Iic_union_Ioi
  refine ⟨fun i => ?_, fun i j hij => ?_, ?_⟩
  · -- Each piece is measurable (either Iic t or Ioi t).
    -- `show` uses definitional equality to expose the underlying if-expression.
    fin_cases i
    · show MeasurableSet (if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Ioi t else Iic t)
      split_ifs <;> assumption
    · show MeasurableSet (if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Iic t else Ioi t)
      split_ifs <;> assumption
  · -- Distinct agents receive disjoint pieces
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · show Disjoint (if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Ioi t else Iic t)
                    (if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Iic t else Ioi t)
      split_ifs with h
      · exact hdLR.symm
      · exact hdLR
    · show Disjoint (if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Iic t else Ioi t)
                    (if μ 1 (Iic t) ≥ μ 1 (Ioi t) then Ioi t else Iic t)
      split_ifs with h
      · exact hdLR
      · exact hdLR.symm
    · exact absurd rfl hij
  · -- The two pieces cover the entire cake
    ext x
    simp only [mem_iUnion, mem_univ, iff_true]
    have hx : x ∈ Iic t ∨ x ∈ Ioi t :=
      (mem_union x (Iic t) (Ioi t)).mp (hcov ▸ mem_univ x)
    by_cases h : μ 1 (Iic t) ≥ μ 1 (Ioi t)
    · -- cutter gets Ioi, chooser gets Iic
      rcases hx with hx | hx
      · exact ⟨1, by rw [cutAndChooseAlloc_one, if_pos h]; exact hx⟩
      · exact ⟨0, by rw [cutAndChooseAlloc_zero, if_pos h]; exact hx⟩
    · -- cutter gets Iic, chooser gets Ioi
      rcases hx with hx | hx
      · exact ⟨0, by rw [cutAndChooseAlloc_zero, if_neg h]; exact hx⟩
      · exact ⟨1, by rw [cutAndChooseAlloc_one, if_neg h]; exact hx⟩

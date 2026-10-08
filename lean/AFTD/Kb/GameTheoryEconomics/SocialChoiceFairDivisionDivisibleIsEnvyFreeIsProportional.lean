import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleIsAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleIsEnvyFree
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleIsProportional
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureValuationValEmpty

/-!
# SocialChoice.FairDivision.Divisible.IsEnvyFree.isProportional

Topic: fair_division   Node: fe98590e7b80

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.IsEnvyFree.isProportional`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**EF implies proportional** for `MeasureValuation` partitions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
/-- **EF implies proportional** for `MeasureValuation` partitions. -/
theorem SocialChoice.FairDivision.Divisible.IsEnvyFree.isProportional
    {N Ω : Type*} [MeasurableSpace Ω] [Fintype N]
    (μ : N → Measure Ω)
    (A : Allocation N Ω)
    (ha : IsAllocation A)
    (hef : IsEnvyFree (MeasureValuation μ) A) :
    IsProportional (Fintype.card N) (MeasureValuation μ) A := by
  intro i
  calc μ i Set.univ
      = μ i (⋃ j, A j) := by rw [ha.cover]
    _ = ∑' j, μ i (A j) :=
          measure_iUnion (fun ⦃j k⦄ hjk => ha.disjoint j k hjk) ha.measurable
    _ = ∑ j : N, μ i (A j) := tsum_fintype _
    _ ≤ ∑ j : N, μ i (A i) := Finset.sum_le_sum fun j _ => hef i j
    _ = Fintype.card N * μ i (A i) := by
          simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

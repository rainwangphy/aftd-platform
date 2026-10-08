import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureInstanceIsEnvyFree
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCardinalInstanceIsEnvyFree
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureInstanceToCardinalInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureValuationValEmpty

/-!
# SocialChoice.FairDivision.Divisible.MeasureInstance.isEnvyFree_iff_toCardinalInstance_isEnvyFree

Topic: fair_division   Node: b14f1995590b

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.MeasureInstance.isEnvyFree_iff_toCardinalInstance_isEnvyFree`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/Instance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For finite measure instances, the raw `ENNReal` envy-freeness predicate agrees with the real-valued cardinal predicate induced by `toReal`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
/-- For finite measure instances, the raw `ENNReal` envy-freeness predicate agrees with the real-valued cardinal predicate induced by `toReal`. -/
theorem SocialChoice.FairDivision.Divisible.MeasureInstance.isEnvyFree_iff_toCardinalInstance_isEnvyFree
    {N Ω : Type*} [MeasurableSpace Ω] [Fintype N]
    (I : MeasureInstance N Ω) [∀ i, IsFiniteMeasure (I.measure i)]
    (A : Allocation N Ω) :
    I.IsEnvyFree A ↔ I.toCardinalInstance.IsEnvyFree A := by
  constructor
  · intro h i j
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mpr (h i j)
  · intro h i j
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _)).mp (h i j)

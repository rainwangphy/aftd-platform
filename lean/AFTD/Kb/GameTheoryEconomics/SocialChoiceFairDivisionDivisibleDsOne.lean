import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleDubinsSpanierProp
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleIsAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleIsProportional
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCakeValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureValuationValEmpty

/-!
# SocialChoice.FairDivision.Divisible.ds_one

Topic: fair_division   Node: b4d2cea8067b

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.ds_one`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/DubinsSpanier.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Base case: 1 agent receives the whole cake. Proportionality holds trivially on the whole unit interval.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped unitInterval in
/-- Base case: 1 agent receives the whole cake. Proportionality holds trivially on the whole unit interval. -/
lemma SocialChoice.FairDivision.Divisible.ds_one : DubinsSpanierProp 1 := by
  intro μ _ _
  refine ⟨fun _ => Set.univ, ⟨fun i => ?_, fun i j hij => ?_, ?_⟩, fun i => ?_⟩
  · -- measurability
    fin_cases i; exact MeasurableSet.univ
  · -- disjointness
    (fin_cases i; fin_cases j; exact absurd rfl hij)
  · -- cover
    simp [Set.iUnion_const]
  · -- proportionality: μ 0 univ ≤ 1 * μ 0 univ
    fin_cases i; simp [MeasureValuation]

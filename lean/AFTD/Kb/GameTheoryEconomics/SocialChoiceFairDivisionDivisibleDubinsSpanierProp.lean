import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleIsAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleIsProportional
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureValuationValEmpty

/-!
# SocialChoice.FairDivision.Divisible.DubinsSpanierProp

Topic: fair_division   Node: f0e43c423616

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.DubinsSpanierProp`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/DubinsSpanier.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The inductive predicate for the Dubins–Spanier algorithm: for n agents indexed by `Fin n`, a complete proportional allocation exists.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped unitInterval in
/-- The inductive predicate for the Dubins–Spanier algorithm: for n agents indexed by `Fin n`, a complete proportional allocation exists. -/
noncomputable def SocialChoice.FairDivision.Divisible.DubinsSpanierProp (n : ℕ) : Prop :=
  ∀ (μ : Fin n → Measure I),
    (∀ i, IsFiniteMeasure (μ i)) →
    (∀ i, NoAtoms (μ i)) →
    ∃ A : Allocation (Fin n) I,
      IsAllocation A ∧ IsProportional n (MeasureValuation μ) A

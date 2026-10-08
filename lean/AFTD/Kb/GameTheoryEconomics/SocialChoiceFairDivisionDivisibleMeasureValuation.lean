import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCakeValuation

/-!
# SocialChoice.FairDivision.Divisible.MeasureValuation

Topic: fair_division   Node: 6452da793f3d

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.MeasureValuation`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/Valuation.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A measure-based cake valuation: each agent's value for a piece is given by their personal measure `μ i` on the cake `Ω`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
/-- A measure-based cake valuation: each agent's value for a piece is given by their personal measure `μ i` on the cake `Ω`. -/
noncomputable def SocialChoice.FairDivision.Divisible.MeasureValuation {N Ω : Type*} [MeasurableSpace Ω]
    (μ : N → MeasureTheory.Measure Ω) : CakeValuation N Ω ENNReal :=
  ⟨fun i S => μ i S⟩

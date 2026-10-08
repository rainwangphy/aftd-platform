import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleMeasureInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCardinalInstance

/-!
# SocialChoice.FairDivision.Divisible.MeasureInstance.toCardinalInstance

Topic: fair_division   Node: 3c86916fd2f2

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.MeasureInstance.toCardinalInstance`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/Instance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The real-valued cardinal instance induced by measure values.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
/-- The real-valued cardinal instance induced by measure values. -/
noncomputable def SocialChoice.FairDivision.Divisible.MeasureInstance.toCardinalInstance {N Ω : Type*} [MeasurableSpace Ω]
    (I : MeasureInstance N Ω) : CardinalInstance N Ω where
  utility := fun i S => (I.measure i S).toReal

import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Pref
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp
import AFTD.Kb.GameTheoryEconomics.SocialChoiceInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionInstance

/-!
# SocialChoice.FairDivision.Divisible.Instance

Topic: fair_division   Node: a635c62d07bb

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.Instance`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/Instance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An ordinal divisible-goods instance. The cake is represented by the ambient measurable space `Ω`, and shares are subsets of `Ω`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
/-- An ordinal divisible-goods instance. The cake is represented by the ambient measurable space `Ω`, and shares are subsets of `Ω`. -/
structure SocialChoice.FairDivision.Divisible.Instance (N Ω : Type*) where
  /-- Each agent's ordinal preference over cake pieces. -/
  sharePref : N → Pref (Set Ω)

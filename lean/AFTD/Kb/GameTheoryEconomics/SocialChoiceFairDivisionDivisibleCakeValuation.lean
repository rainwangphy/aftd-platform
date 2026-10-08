import AFTD.Prelude
import AFTD.Kb.Tcs.V

/-!
# SocialChoice.FairDivision.Divisible.CakeValuation

Topic: fair_division   Node: 1489e5e651cf

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.CakeValuation`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/Valuation.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An abstract cake valuation assigns a value in `V` to each agent-piece pair.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
/-- An abstract cake valuation assigns a value in `V` to each agent-piece pair. -/
structure SocialChoice.FairDivision.Divisible.CakeValuation (N Ω V : Type*) where
  /-- The valuation function: agent × cake-piece → value. -/
  val : N → Set Ω → V

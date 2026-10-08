import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionAllocation
import AFTD.Kb.GameTheoryEconomics.Pref
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# SocialChoice.FairDivision.Instance

Topic: fair_division   Node: 013207822bf9

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Instance`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A fully general fair-division instance. This allows preferences over complete allocations, so it can express externalities or other global allocation comparisons.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A fully general fair-division instance. This allows preferences over complete allocations, so it can express externalities or other global allocation comparisons. -/
structure SocialChoice.FairDivision.Instance (N R S : Type*) where
  /-- Resource-side data for the instance. -/
  resource : R
  /-- Feasible allocations for the given resource data. -/
  feasible : Allocation N S → Prop
  /-- Each agent's preference over complete allocations. -/
  pref : N → Pref (Allocation N S)

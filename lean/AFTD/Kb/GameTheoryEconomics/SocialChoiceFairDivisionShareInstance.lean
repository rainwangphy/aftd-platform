import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionAllocation
import AFTD.Kb.GameTheoryEconomics.Pref
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# SocialChoice.FairDivision.ShareInstance

Topic: fair_division   Node: 5188f4594182

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.ShareInstance`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A no-externality fair-division instance where each agent ranks only the share they personally receive.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A no-externality fair-division instance where each agent ranks only the share they personally receive. -/
structure SocialChoice.FairDivision.ShareInstance (N R S : Type*) where
  /-- Resource-side data for the instance. -/
  resource : R
  /-- Feasible allocations for the given resource data. -/
  feasible : Allocation N S → Prop
  /-- Each agent's preference over individual shares. -/
  sharePref : N → Pref S

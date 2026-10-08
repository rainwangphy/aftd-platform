import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique

/-!
# SocialChoice.FairDivision.CardinalInstance

Topic: fair_division   Node: 26c7955c5b2c

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.CardinalInstance`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Cardinal.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A real-valued cardinal fair-division instance in the standard no-externality model.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A real-valued cardinal fair-division instance in the standard no-externality model. -/
structure SocialChoice.FairDivision.CardinalInstance (N R S : Type*) where
  /-- Resource-side data for the instance. -/
  resource : R
  /-- Feasible allocations for the given resource data. -/
  feasible : Allocation N S → Prop
  /-- Utility assigned by each agent to each individual share. -/
  utility : N → S → ℝ

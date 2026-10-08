import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionAllocation

/-!
# SocialChoice.FairDivision.SolutionConcept

Topic: fair_division   Node: 505aa5d10a3b

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.SolutionConcept`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A fair-division solution concept is a predicate selecting acceptable allocations relative to a fully general instance.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A fair-division solution concept is a predicate selecting acceptable allocations relative to a fully general instance. -/
def SocialChoice.FairDivision.SolutionConcept (N R S : Type*) :=
  Instance N R S → Allocation N S → Prop

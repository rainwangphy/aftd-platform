import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionAllocation

/-!
# SocialChoice.FairDivision.Divisible.Allocation

Topic: fair_division   Node: f26986e8b020

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.Allocation`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/Allocation.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A divisible allocation assigns each agent `i : N` a piece (a measurable subset) of the cake `Ω`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
/-- A divisible allocation assigns each agent `i : N` a piece (a measurable subset) of the cake `Ω`. -/
abbrev SocialChoice.FairDivision.Divisible.Allocation (N Ω : Type*) := SocialChoice.FairDivision.Allocation N (Set Ω)

import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleAllocation

/-!
# SocialChoice.FairDivision.Divisible.IsAllocation

Topic: fair_division   Node: 7959ddb66e4c

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.IsAllocation`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/Allocation.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A complete divisible allocation is a measurable partition of the cake.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
/-- A complete divisible allocation is a measurable partition of the cake. -/
structure SocialChoice.FairDivision.Divisible.IsAllocation {N Ω : Type*} [MeasurableSpace Ω] [Fintype N]
    (A : Allocation N Ω) : Prop where
  /-- Each piece is a measurable set. -/
  measurable : ∀ i : N, MeasurableSet (A i)
  /-- Distinct agents receive disjoint pieces. -/
  disjoint   : ∀ i j : N, i ≠ j → Disjoint (A i) (A j)
  /-- Every point of the cake belongs to some agent's piece. -/
  cover      : ⋃ i : N, A i = Set.univ

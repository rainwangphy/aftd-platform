import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleAllocation

/-!
# SocialChoice.FairDivision.Divisible.IsContiguousAllocation

Topic: fair_division   Node: 4417a125a503

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.IsContiguousAllocation`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/Allocation.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A **contiguous allocation** on `ℝ`: each agent's piece is an interval (an order-connected subset of `ℝ`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
/-- A **contiguous allocation** on `ℝ`: each agent's piece is an interval (an order-connected subset of `ℝ`). -/
def SocialChoice.FairDivision.Divisible.IsContiguousAllocation {N : Type*} (A : Allocation N ℝ) : Prop :=
  ∀ i : N, (A i).OrdConnected

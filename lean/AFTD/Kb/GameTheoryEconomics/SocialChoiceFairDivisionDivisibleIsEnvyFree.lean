import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCakeValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleAllocation

/-!
# SocialChoice.FairDivision.Divisible.IsEnvyFree

Topic: fair_division   Node: 39e93ae10ec5

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.IsEnvyFree`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Envy-free (EF): every agent weakly prefers their own piece over any other agent's piece. `∀ i j, μ_i(A_j) ≤ μ_i(A_i)`. For divisible goods with non-atomic measures, EF allocations always exist. This is the key difference from the indivisible setting where EF need not exist.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
/-- Envy-free (EF): every agent weakly prefers their own piece over any other agent's piece. `∀ i j, μ_i(A_j) ≤ μ_i(A_i)`. For divisible goods with non-atomic measures, EF allocations always exist. This is the key difference from the indivisible setting where EF need not exist. -/
def SocialChoice.FairDivision.Divisible.IsEnvyFree {N Ω V : Type*} [Preorder V]
    (μ : CakeValuation N Ω V) (A : Allocation N Ω) : Prop :=
  ∀ i j : N, μ.val i (A j) ≤ μ.val i (A i)

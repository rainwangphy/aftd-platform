import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleCakeValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionDivisibleAllocation
import AFTD.Kb.Tcs.V

/-!
# SocialChoice.FairDivision.Divisible.IsProportional

Topic: fair_division   Node: b385f4ac4aff

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Divisible.IsProportional`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Divisible/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Proportional (PROP): each agent values their piece at least `1 / n` of the whole cake. Stated as `μ_i(Ω) ≤ n * μ_i(A_i)` to avoid division.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
/-- Proportional (PROP): each agent values their piece at least `1 / n` of the whole cake. Stated as `μ_i(Ω) ≤ n * μ_i(A_i)` to avoid division. -/
def SocialChoice.FairDivision.Divisible.IsProportional {N Ω V : Type*} [Preorder V] [Semiring V] (n : ℕ)
    (μ : CakeValuation N Ω V) (A : Allocation N Ω) : Prop :=
  ∀ i : N, μ.val i Set.univ ≤ (n : V) * μ.val i (A i)

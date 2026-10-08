import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsLinearUtility
import AFTD.Kb.GameTheoryEconomics.Lottery
import AFTD.Kb.GameTheoryEconomics.LotteryExpectedValue
import AFTD.Kb.GameTheoryEconomics.LotteryExpectedValueMix
import AFTD.Kb.Optimization.StdSimplexMixApply
import AFTD.Kb.Optimization.WsumPureApply

/-!
# expectedValue_isLinearUtility

Topic: general_equilibrium   Node: 56068b46dcd5

Provenance: formalization of a published result. Source: EconCSLib, `expectedValue_isLinearUtility`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/Lottery.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Expected value (with respect to a fixed payoff function) is a linear utility.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
set_option linter.unusedSectionVars false in
/-- Expected value (with respect to a fixed payoff function) is a linear utility. -/
theorem expectedValue_isLinearUtility {O : Type*} [Fintype O] (f : O → 𝕜) :
    IsLinearUtility (𝕜 := 𝕜) (fun L => Lottery.expectedValue L f) := by
  intro α hα₀ hα₁ L₁ L₂
  exact Lottery.expectedValue_mix α hα₀ hα₁ L₁ L₂ f

import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LotteryExpectedValue
import AFTD.Kb.GameTheoryEconomics.LotteryPure
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.Optimization.StdSimplexPureApply

/-!
# Lottery.expectedValue_pure

Topic: general_equilibrium   Node: 805a4a6bce22

Provenance: formalization of a published result. Source: EconCSLib, `Lottery.expectedValue_pure`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/Lottery.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Expected value of a pure lottery equals the outcome value.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
set_option linter.unusedSectionVars false in
variable {O : Type*} [Fintype O] in
/-- Expected value of a pure lottery equals the outcome value. -/
theorem Lottery.expectedValue_pure [DecidableEq O] (o₀ : O) (f : O → 𝕜) :
    Lottery.expectedValue (Lottery.pure (𝕜 := 𝕜) o₀) f = f o₀ :=
  wsum_pure_apply o₀ f

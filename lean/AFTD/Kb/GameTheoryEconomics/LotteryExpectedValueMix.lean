import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Lottery
import AFTD.Kb.GameTheoryEconomics.LotteryExpectedValue
import AFTD.Kb.GameTheoryEconomics.LotteryMix
import AFTD.Kb.Optimization.WsumMix
import AFTD.Kb.Optimization.StdSimplexMixApply
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Lottery.expectedValue_mix

Topic: general_equilibrium   Node: 4d6fa46002d3

Provenance: formalization of a published result. Source: EconCSLib, `Lottery.expectedValue_mix`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/Lottery.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Linearity of expected value** under convex combination. `E[mix α L₁ L₂] = α · E[L₁] + (1-α) · E[L₂]` This is the key property corresponding to [MSZ Axiom 2.16] (simplification of compound lotteries).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
set_option linter.unusedSectionVars false in
variable {O : Type*} [Fintype O] in
/-- **Linearity of expected value** under convex combination. `E[mix α L₁ L₂] = α · E[L₁] + (1-α) · E[L₂]` This is the key property corresponding to [MSZ Axiom 2.16] (simplification of compound lotteries). -/
theorem Lottery.expectedValue_mix (α : 𝕜) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (L₁ L₂ : Lottery 𝕜 O) (f : O → 𝕜) :
    Lottery.expectedValue (Lottery.mix α hα₀ hα₁ L₁ L₂) f =
    α * Lottery.expectedValue L₁ f + (1 - α) * Lottery.expectedValue L₂ f :=
  wsum_mix α hα₀ hα₁ L₁ L₂ f

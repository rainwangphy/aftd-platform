import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Lottery
import AFTD.Kb.GameTheoryEconomics.LotteryMix
import AFTD.Kb.Optimization.StdSimplexMixApply

/-!
# IsLinearUtility

Topic: general_equilibrium   Node: 2a083cbdb0bb

Provenance: formalization of a published result. Source: EconCSLib, `IsLinearUtility`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/Lottery.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A utility function `u` is linear (in the vNM sense) if it respects compound lottery simplification: `u([α(L₁), (1-α)(L₂)]) = α · u(L₁) + (1-α) · u(L₂)`. Equivalently, `u(L) = E_L[u ∘ outcome]` for some function on outcomes. [MSZ Definition 2.10]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
set_option linter.unusedSectionVars false in
/-- A utility function `u` is linear (in the vNM sense) if it respects compound lottery simplification: `u([α(L₁), (1-α)(L₂)]) = α · u(L₁) + (1-α) · u(L₂)`. Equivalently, `u(L) = E_L[u ∘ outcome]` for some function on outcomes. [MSZ Definition 2.10] -/
def IsLinearUtility {O : Type*} [Fintype O]
    (u : Lottery 𝕜 O → 𝕜) : Prop :=
  ∀ (α : 𝕜) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (L₁ L₂ : Lottery 𝕜 O),
    u (Lottery.mix α hα₀ hα₁ L₁ L₂) = α * u L₁ + (1 - α) * u L₂

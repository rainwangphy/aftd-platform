import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Lottery
import AFTD.Kb.Optimization.StdSimplexMix
import AFTD.Kb.Optimization.StdSimplexMixApply

/-!
# Lottery.mix

Topic: general_equilibrium   Node: d6b5e2c89f46

Provenance: formalization of a published result. Source: EconCSLib, `Lottery.mix`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/Lottery.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Convex combination of two lotteries: the compound lottery `[α(L₁), (1-α)(L₂)]` after simplification. [MSZ Axiom 2.16] Alias of `stdSimplex.mix`: `mix α L₁ L₂ = α · L₁ + (1-α) · L₂` pointwise.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
set_option linter.unusedSectionVars false in
/-- Convex combination of two lotteries: the compound lottery `[α(L₁), (1-α)(L₂)]` after simplification. [MSZ Axiom 2.16] Alias of `stdSimplex.mix`: `mix α L₁ L₂ = α · L₁ + (1-α) · L₂` pointwise. -/
abbrev Lottery.mix {O : Type*} [Fintype O]
    (α : 𝕜) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (L₁ L₂ : Lottery 𝕜 O) : Lottery 𝕜 O :=
  stdSimplex.mix α hα₀ hα₁ L₁ L₂

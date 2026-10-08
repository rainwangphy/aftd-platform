import AFTD.Prelude
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.Optimization.WsumPureApply

/-!
# IsRiskNeutral

Topic: general_equilibrium   Node: 79b0c595ba62

Provenance: formalization of a published result. Source: EconCSLib, `IsRiskNeutral`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Risk neutrality for lotteries over a finite index set `I`: `u(∑ pᵢ·xᵢ) = ∑ pᵢ·u(xᵢ)`. Equivalent to `u` being affine. [MSZ 2.27]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
set_option linter.unusedSectionVars false in
/-- Risk neutrality for lotteries over a finite index set `I`: `u(∑ pᵢ·xᵢ) = ∑ pᵢ·u(xᵢ)`. Equivalent to `u` being affine. [MSZ 2.27] -/
def IsRiskNeutral {I : Type*} [Fintype I] (u : 𝕜 → 𝕜) : Prop :=
  ∀ (p : stdSimplex 𝕜 I) (x : I → 𝕜),
    u (wsum p x) = wsum p (u ∘ x)

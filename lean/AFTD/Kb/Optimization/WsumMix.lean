import AFTD.Prelude
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.Optimization.StdSimplexMix
import AFTD.Kb.Optimization.StdSimplexMixApply

/-!
# wsum_mix

Topic: lp_duality   Node: 929dd20cebaf

Provenance: formalization of a published result. Source: EconCSLib, `wsum_mix`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Simplex.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Bilinearity of `wsum` over `stdSimplex.mix`: `wsum (mix α x y) f = α · wsum x f + (1-α) · wsum y f`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] in
set_option linter.unusedSectionVars false in
/-- Bilinearity of `wsum` over `stdSimplex.mix`: `wsum (mix α x y) f = α · wsum x f + (1-α) · wsum y f`. -/
theorem wsum_mix (α : 𝕜) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (x y : stdSimplex 𝕜 I) (f : I → 𝕜) :
    wsum (stdSimplex.mix α hα₀ hα₁ x y) f =
      α * wsum x f + (1 - α) * wsum y f := by
  change (∑ i, (α * x.val i + (1 - α) * y.val i) * f i)
       = α * (∑ i, x.val i * f i) + (1 - α) * (∑ i, y.val i * f i)
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _; ring

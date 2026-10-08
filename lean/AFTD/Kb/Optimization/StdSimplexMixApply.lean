import AFTD.Prelude
import AFTD.Kb.Optimization.StdSimplexMix

/-!
# stdSimplex.mix_apply

Topic: lp_duality   Node: e6d02ab6e5fa

Provenance: formalization of a published result. Source: EconCSLib, `stdSimplex.mix_apply`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Simplex.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

stdSimplex.mix_apply
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] in
set_option linter.unusedSectionVars false in
@[simp]
theorem stdSimplex.mix_apply (α : 𝕜) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1)
    (x y : stdSimplex 𝕜 I) (i : I) :
    (stdSimplex.mix α hα₀ hα₁ x y).val i = α * x.val i + (1 - α) * y.val i := rfl

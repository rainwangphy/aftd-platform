import AFTD.Prelude
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.Optimization.StdSimplexPure

/-!
# wsum_pure

Topic: lp_duality   Node: e642e2899d53

Provenance: formalization of a published result. Source: EconCSLib, `wsum_pure`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Simplex.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Weighted sum with point mass at `i₀` equals `f i₀`. Legacy form using the inline anonymous-structure point mass. New code should prefer `stdSimplex.pure` together with `wsum_pure_apply`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] in
set_option linter.unusedSectionVars false in
/-- Weighted sum with point mass at `i₀` equals `f i₀`. Legacy form using the inline anonymous-structure point mass. New code should prefer `stdSimplex.pure` together with `wsum_pure_apply`. -/
theorem wsum_pure [DecidableEq I] (i₀ : I) (f : I → 𝕜) :
    wsum ⟨fun i => if i = i₀ then 1 else 0,
          fun i => by simp only; split_ifs <;> norm_num,
          by simp [Finset.sum_ite_eq', Finset.mem_univ]⟩ f = f i₀ :=
  wsum_pure_apply (𝕜 := 𝕜) i₀ f

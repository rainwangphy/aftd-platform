import AFTD.Prelude

/-!
# stdSimplex.pure

Topic: lp_duality   Node: 60fad6c4f0cf

Provenance: formalization of a published result. Source: EconCSLib, `stdSimplex.pure`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Simplex.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Point-mass simplex element at `i₀`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] in
set_option linter.unusedSectionVars false in
/-- Point-mass simplex element at `i₀`. -/
def stdSimplex.pure [DecidableEq I] (i₀ : I) : stdSimplex 𝕜 I where
  val i := if i = i₀ then 1 else 0
  property := ⟨fun i => by simp only; split_ifs <;> norm_num,
               by simp [Finset.sum_ite_eq', Finset.mem_univ]⟩

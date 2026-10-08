import AFTD.Prelude
import AFTD.Kb.Optimization.StdSimplexAffineCombination

/-!
# stdSimplex.affineCombination_eq_linearCombination

Topic: lp_duality   Node: 9022957d9d79

Provenance: formalization of a published result. Source: EconCSLib, `stdSimplex.affineCombination_eq_linearCombination`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Simplex.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

In a module, simplex affine combinations are Mathlib finite linear combinations.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] in
set_option linter.unusedSectionVars false in
/-- In a module, simplex affine combinations are Mathlib finite linear combinations. -/
@[simp]
theorem stdSimplex.affineCombination_eq_linearCombination {k V I : Type*}
    [Ring k] [PartialOrder k] [Fintype I]
    [AddCommGroup V] [Module k V]
    (x : stdSimplex k I) (p : I → V) :
    affineCombination x p = Fintype.linearCombination k p x := by
  simp [affineCombination, Fintype.linearCombination_apply,
    Finset.affineCombination_eq_linear_combination, stdSimplex.sum_eq_one x]

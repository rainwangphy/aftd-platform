import AFTD.Prelude
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.Optimization.WsumSmul

/-!
# Loomis.wsum_const_mul

Topic: equilibria   Node: 61188395445d

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.wsum_const_mul`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Weight a constant multiple under `wsum`: `wsum z (c · f) = c · wsum z f`. A direct unfold of `wsum_smul`, restated here so chained rewrites match the shape used in the weak-duality proof.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Weight a constant multiple under `wsum`: `wsum z (c · f) = c · wsum z f`. A direct unfold of `wsum_smul`, restated here so chained rewrites match the shape used in the weak-duality proof. -/
theorem Loomis.wsum_const_mul {K : Type*} [Fintype K] (z : stdSimplex ℝ K)
    (c : ℝ) (f : K → ℝ) :
    wsum z (fun a => c * f a) = c * wsum z f := by
  change (∑ a, z.val a * (c * f a)) = c * (∑ a, z.val a * f a)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro a _
  ring

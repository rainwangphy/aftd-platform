import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisRowOffset
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.GameTheoryEconomics.LoomisBy
import AFTD.Kb.GameTheoryEconomics.LoomisAy
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.rowOffset_eq_wsum

Topic: equilibria   Node: 88eca0ecec93

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.rowOffset_eq_wsum`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`rowOffset` is a `wsum` of `μ B i j - A i j` over `j`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- `rowOffset` is a `wsum` of `μ B i j - A i j` over `j`. -/
theorem Loomis.rowOffset_eq_wsum (A B : I → J → ℝ) (mu : ℝ)
    (y : stdSimplex ℝ J) (i : I) :
    rowOffset A B mu y i = wsum y (fun j => mu * B i j - A i j) := by
  unfold rowOffset Ay By
  change mu * (∑ j, y.val j * B i j) - (∑ j, y.val j * A i j)
      = ∑ j, y.val j * (mu * B i j - A i j)
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

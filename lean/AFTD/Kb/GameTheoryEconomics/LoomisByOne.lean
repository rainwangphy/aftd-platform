import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisBy
import AFTD.Kb.Optimization.WsumConst
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.By_one

Topic: equilibria   Node: c9f6f8e449af

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.By_one`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Loomis.By_one
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
theorem Loomis.By_one (y : stdSimplex ℝ J) (i : I) :
    By (fun (_ : I) (_ : J) => (1 : ℝ)) y i = 1 := by
  unfold By
  exact wsum_const y 1

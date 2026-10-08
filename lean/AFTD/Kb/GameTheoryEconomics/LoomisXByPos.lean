import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisIsPositive
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.GameTheoryEconomics.LoomisBy
import AFTD.Kb.Optimization.WsumPos
import AFTD.Kb.GameTheoryEconomics.LoomisByPos
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.xBy_pos

Topic: equilibria   Node: 884051a58008

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.xBy_pos`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Positivity of the bilinear pairing `xBy = ∑ᵢⱼ xᵢ Bᵢⱼ yⱼ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Positivity of the bilinear pairing `xBy = ∑ᵢⱼ xᵢ Bᵢⱼ yⱼ`. -/
theorem Loomis.xBy_pos {B : I → J → ℝ} (hB : IsPositive B)
    (x : stdSimplex ℝ I) (y : stdSimplex ℝ J) :
    0 < wsum x (fun i => By B y i) :=
  wsum_pos x (fun i => By_pos hB y i)

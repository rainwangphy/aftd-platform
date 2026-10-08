import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisIsPositive
import AFTD.Kb.GameTheoryEconomics.LoomisLamBAux
import AFTD.Kb.GameTheoryEconomics.LoomisLamB0
import AFTD.Kb.GameTheoryEconomics.LoomisLamBAuxBddAbove
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.lamB.aux.le_lamB0

Topic: equilibria   Node: 38239a7eda6b

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.lamB.aux.le_lamB0`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Every `lamB.aux` value is bounded by the supremum `lamB0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Every `lamB.aux` value is bounded by the supremum `lamB0`. -/
theorem Loomis.lamB.aux.le_lamB0 {A B : I → J → ℝ} (hB : IsPositive B)
    (x : stdSimplex ℝ I) :
    lamB.aux A B x ≤ lamB0 A B :=
  le_ciSup (bddAbove_def.2 (by
    obtain ⟨C, hC⟩ := lamB.aux.bddAbove hB
    exact ⟨C, by rintro r ⟨x, rfl⟩; exact hC x⟩)) x

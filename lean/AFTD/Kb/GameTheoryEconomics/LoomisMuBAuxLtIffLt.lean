import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisMuBAux
import AFTD.Kb.GameTheoryEconomics.LoomisRowRatio
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.muB.aux_lt_iff_lt

Topic: equilibria   Node: d589571a47a3

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.muB.aux_lt_iff_lt`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Characterisation: `muB.aux A B y < c` iff every row ratio is below `c`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Characterisation: `muB.aux A B y < c` iff every row ratio is below `c`. -/
theorem Loomis.muB.aux_lt_iff_lt (A B : I → J → ℝ) (c : ℝ) (y : stdSimplex ℝ J) :
    muB.aux A B y < c ↔ ∀ i, rowRatio A B y i < c := by
  simp [muB.aux, Finset.sup'_lt_iff]

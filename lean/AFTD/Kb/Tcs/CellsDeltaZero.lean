import AFTD.Prelude
import AFTD.Kb.Tcs.Cells
import AFTD.Kb.Tcs.CellsInstZero

/-!
# Cells.delta_zero

Topic: algorithms   Node: 82edc0117828

Provenance: formalization of a published result. Source: EconCSLib, `Cells.delta_zero`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/CostM/Cells.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cells.delta_zero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSimpArgs false in
@[simp] theorem Cells.delta_zero : (0 : Cells).delta = 0 := rfl

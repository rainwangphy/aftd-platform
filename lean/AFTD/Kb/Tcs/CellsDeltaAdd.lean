import AFTD.Prelude
import AFTD.Kb.Tcs.Cells
import AFTD.Kb.Tcs.CellsInstAdd
import AFTD.Kb.Tcs.CellsInstZero

/-!
# Cells.delta_add

Topic: algorithms   Node: 9c08884864ba

Provenance: formalization of a published result. Source: EconCSLib, `Cells.delta_add`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/CostM/Cells.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cells.delta_add
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSimpArgs false in
@[simp] theorem Cells.delta_add (a b : Cells) :
    (a + b).delta = a.delta + b.delta := rfl

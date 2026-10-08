import AFTD.Prelude
import AFTD.Kb.Tcs.Cells
import AFTD.Kb.Tcs.CellsAlloc
import AFTD.Kb.Tcs.CellsPeakAlloc
import AFTD.Kb.Tcs.CellsInstZero
import AFTD.Kb.Tcs.CellsInstAdd
import AFTD.Kb.Tcs.CellsInstAddMonoid

/-!
# Cells.delta_alloc

Topic: algorithms   Node: 9e0b546bb094

Provenance: formalization of a published result. Source: EconCSLib, `Cells.delta_alloc`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/CostM/Cells.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cells.delta_alloc
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSimpArgs false in
@[simp] theorem Cells.delta_alloc (n : ℕ) : (alloc n).delta = n := rfl

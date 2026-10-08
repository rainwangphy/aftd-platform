import AFTD.Prelude
import AFTD.Kb.Tcs.Cells
import AFTD.Kb.Tcs.CellsAlloc
import AFTD.Kb.Tcs.CellsInstZero
import AFTD.Kb.Tcs.CellsInstAdd
import AFTD.Kb.Tcs.CellsInstAddMonoid

/-!
# Cells.peak_alloc

Topic: algorithms   Node: 6456a6c0f295

Provenance: formalization of a published result. Source: EconCSLib, `Cells.peak_alloc`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/CostM/Cells.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cells.peak_alloc
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSimpArgs false in
@[simp] theorem Cells.peak_alloc  (n : ℕ) : (alloc n).peak  = n := rfl

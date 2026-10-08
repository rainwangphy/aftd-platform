import AFTD.Prelude
import AFTD.Kb.Tcs.Cells
import AFTD.Kb.Tcs.CellsInstZero
import AFTD.Kb.Tcs.CellsInstAdd
import AFTD.Kb.Tcs.CellsInstAddMonoid

/-!
# Cells.alloc

Topic: algorithms   Node: bb23025d5f91

Provenance: formalization of a published result. Source: EconCSLib, `Cells.alloc`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/CostM/Cells.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Allocate `n` cells: peak and delta both rise by `n`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSimpArgs false in
/-- Allocate `n` cells: peak and delta both rise by `n`. -/
def Cells.alloc (n : ℕ) : Cells where
  peak  := n
  delta := n
  zero_le_peak  := Int.natCast_nonneg _
  delta_le_peak := le_refl _

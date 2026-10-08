import AFTD.Prelude
import AFTD.Kb.Tcs.Cells
import AFTD.Kb.Tcs.CellsInstZero
import AFTD.Kb.Tcs.CellsInstAdd
import AFTD.Kb.Tcs.CellsInstAddMonoid

/-!
# Cells.free

Topic: algorithms   Node: f888fc9e0831

Provenance: formalization of a published result. Source: EconCSLib, `Cells.free`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/CostM/Cells.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Release `n` cells: peak unchanged, delta drops by `n`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSimpArgs false in
/-- Release `n` cells: peak unchanged, delta drops by `n`. -/
def Cells.free (n : ℕ) : Cells where
  peak  := 0
  delta := -n
  zero_le_peak  := le_refl _
  delta_le_peak := by
    have : (0 : ℤ) ≤ n := Int.natCast_nonneg _
    linarith

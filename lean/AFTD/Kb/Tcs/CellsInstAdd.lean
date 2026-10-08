import AFTD.Prelude
import AFTD.Kb.Tcs.Cells
import AFTD.Kb.Tcs.CellsInstZero

/-!
# Cells.instAdd

Topic: algorithms   Node: db71e2e5d036

Provenance: formalization of a published result. Source: EconCSLib, `Cells.instAdd`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/CostM/Cells.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cells.instAdd
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSimpArgs false in
instance Cells.instAdd : Add Cells where
  add a b :=
    { peak  := max a.peak (a.delta + b.peak)
      delta := a.delta + b.delta
      zero_le_peak  := le_max_of_le_left a.zero_le_peak
      delta_le_peak := by
        have hb := b.delta_le_peak
        have : a.delta + b.delta ≤ a.delta + b.peak := by linarith
        exact this.trans (le_max_right _ _) }

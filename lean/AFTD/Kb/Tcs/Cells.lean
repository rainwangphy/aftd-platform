import AFTD.Prelude

/-!
# Cells

Topic: algorithms   Node: 6e09902be4b7

Provenance: formalization of a published result. Source: EconCSLib, `Cells`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/CostM/Cells.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Tropical-style cost record: peak occupancy and net delta.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSimpArgs false in
/-- Tropical-style cost record: peak occupancy and net delta. -/
@[ext]
structure Cells where
  /-- Peak occupancy reached during the computation (≥ 0). -/
  peak  : ℤ
  /-- Net change in occupancy from start to end (≤ peak). -/
  delta : ℤ
  /-- Peak is non-negative. -/
  zero_le_peak  : 0 ≤ peak
  /-- Delta never exceeds peak. -/
  delta_le_peak : delta ≤ peak

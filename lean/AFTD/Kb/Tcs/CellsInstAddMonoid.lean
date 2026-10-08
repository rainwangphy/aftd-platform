import AFTD.Prelude
import AFTD.Kb.Tcs.Cells
import AFTD.Kb.Tcs.CellsInstAdd
import AFTD.Kb.Tcs.CellsInstZero
import AFTD.Kb.Tcs.CellsDeltaAdd
import AFTD.Kb.Tcs.CellsDeltaZero
import AFTD.Kb.Tcs.CellsPeakAdd
import AFTD.Kb.Tcs.CellsPeakZero

/-!
# Cells.instAddMonoid

Topic: algorithms   Node: b5c8626dae48

Provenance: formalization of a published result. Source: EconCSLib, `Cells.instAddMonoid`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/CostM/Cells.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cells.instAddMonoid
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSimpArgs false in
instance Cells.instAddMonoid : AddMonoid Cells where
  add_assoc a b c := by
    ext
    · -- peak: max(max p₁ (d₁+p₂)) (d₁+d₂+p₃) = max p₁ (d₁ + max p₂ (d₂+p₃))
      simp only [peak_add, delta_add]
      omega
    · -- delta: associative addition
      simp only [delta_add]
      omega
  zero_add a := by
    ext
    · -- max 0 (0 + a.peak) = a.peak, using 0 ≤ a.peak
      have := a.zero_le_peak
      simp only [peak_add, peak_zero, delta_zero]
      omega
    · simp
  add_zero a := by
    ext
    · -- max a.peak (a.delta + 0) = a.peak, using a.delta ≤ a.peak
      have := a.delta_le_peak
      simp only [peak_add, peak_zero, delta_zero]
      omega
    · simp
  nsmul := nsmulRec

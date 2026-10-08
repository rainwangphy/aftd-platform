import AFTD.Prelude
import AFTD.Kb.Optimization.MixGtOfGtNbh

/-!
# mix_lt_of_lt_nbh

Topic: lp_duality   Node: 21a40249588b

Provenance: formalization of a published result. Source: EconCSLib, `mix_lt_of_lt_nbh`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Simplex.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Dual: strictly interior `t` keeping `t·x + (1-t)·y < c`, given `x < c`. Obtained from `mix_gt_of_gt_nbh` by negating `x, y, c`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] in
set_option linter.unusedSectionVars false in
/-- Dual: strictly interior `t` keeping `t·x + (1-t)·y < c`, given `x < c`. Obtained from `mix_gt_of_gt_nbh` by negating `x, y, c`. -/
theorem mix_lt_of_lt_nbh (x y c : 𝕜) (H : x < c) :
    ∃ t : 𝕜, 0 < t ∧ t < 1 ∧ t * x + (1 - t) * y < c := by
  obtain ⟨t, ht0, ht1, hgt⟩ := mix_gt_of_gt_nbh (-x) (-y) (-c) (by linarith)
  refine ⟨t, ht0, ht1, ?_⟩
  have hneg : t * (-x) + (1 - t) * (-y) = -(t * x + (1 - t) * y) := by ring
  rw [hneg] at hgt
  linarith

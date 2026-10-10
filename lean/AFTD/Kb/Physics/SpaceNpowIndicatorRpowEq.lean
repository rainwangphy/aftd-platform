import AFTD.Prelude

/-!
# Space.npow_indicator_rpow_eq

Topic: classical_mechanics   Node: d166b3baf104

Provenance: formalization of a published result. Source: Physlib, `Space.npow_indicator_rpow_eq`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Integrals/NormPow.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Space.npow_indicator_rpow_eq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory SchwartzMap in
lemma Space.npow_indicator_rpow_eq {n : ℕ} {s : Set ℝ} (hs : 0 ∉ s) (p : ℝ) :
    (fun r ↦ r ^ n • s.indicator (fun r ↦ r ^ p) r) = s.indicator (fun r ↦ r ^ (n + p)) := by
  ext r
  by_cases hr : r ∈ s
  · grind [Set.indicator_of_mem, smul_eq_mul, add_comm, Real.rpow_add_natCast]
  · simp [hr]

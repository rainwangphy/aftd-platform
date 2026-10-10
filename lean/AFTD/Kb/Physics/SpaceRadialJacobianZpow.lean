import AFTD.Prelude

/-!
# Space.radial_jacobian_zpow

Topic: classical_mechanics   Node: f025e77c42ae

Provenance: formalization of a published result. Source: Physlib, `Space.radial_jacobian_zpow`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Integrals/NormPow.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Space.radial_jacobian_zpow
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory SchwartzMap in
lemma Space.radial_jacobian_zpow
    {d p : ℕ} [NeZero d] {q : ℤ} (hp_int : (p : ℤ) = q + (d : ℤ))
    (hp_pos : 0 < p) {r : ℝ} (hr : 0 < r) :
    r ^ (d - 1) * r ^ q = r ^ (p - 1) := by
  have hz : r ≠ 0 := ne_of_gt hr
  calc
    r ^ (d - 1) * r ^ q
        = r ^ ((d - 1 : ℤ) + q) := by
            rw [← Nat.cast_pred (Nat.pos_of_neZero d), ← zpow_natCast, ← zpow_add₀ hz]
    _ = r ^ ((p - 1 : ℕ) : ℤ) := by
            congr 1; omega
    _ = r ^ (p - 1) := by
            rw [zpow_natCast]

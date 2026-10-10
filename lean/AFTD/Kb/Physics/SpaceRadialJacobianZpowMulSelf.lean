import AFTD.Prelude

/-!
# Space.radial_jacobian_zpow_mul_self

Topic: classical_mechanics   Node: 01baa4be31db

Provenance: formalization of a published result. Source: Physlib, `Space.radial_jacobian_zpow_mul_self`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Integrals/NormPow.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Space.radial_jacobian_zpow_mul_self
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory SchwartzMap in
lemma Space.radial_jacobian_zpow_mul_self
    {d p : ℕ} [NeZero d] {q : ℤ} (hp_int : (p : ℤ) = q + (d : ℤ))
    {r : ℝ} (hr : 0 < r) :
    r ^ (d - 1) * (r ^ q * r) = r ^ p := by
  have hz : r ≠ 0 := ne_of_gt hr
  calc
    r ^ (d - 1) * (r ^ q * r)
        = r ^ (d - 1: ℤ) * (r ^ q * r ^ (1 : ℤ)) := by
            rw [← zpow_natCast, zpow_one, ← Nat.cast_pred (Nat.pos_of_neZero d)]
    _ = r ^ ((d - 1: ℤ) + (q + 1)) := by
            rw [← zpow_add₀ hz q 1, ← zpow_add₀ hz (d - 1: ℤ) (q + 1)]
    _ = r ^ (p : ℤ) := by
            congr 1; omega
    _ = r ^ p := by
            rw [zpow_natCast]

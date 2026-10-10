import AFTD.Prelude

/-!
# Cosmology.SpatialGeometry.mul_sinh_as_div

Topic: cosmology   Node: 82a83ad2091b

Provenance: formalization of a published result. Source: Physlib, `Cosmology.SpatialGeometry.mul_sinh_as_div`. Lean proof by Luis Gabriel C. Bariuan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Cosmology/FLRW/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The limit of `S (Saddle k) r` as `k → ∞` is equal to `S (Flat) r`. First show that `k * sinh(r / k) = sinh(r / k) / (1 / k)` pointwise.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
open scoped Topology in
/-- The limit of `S (Saddle k) r` as `k → ∞` is equal to `S (Flat) r`. First show that `k * sinh(r / k) = sinh(r / k) / (1 / k)` pointwise. -/
lemma Cosmology.SpatialGeometry.mul_sinh_as_div (r k : ℝ) :
    k * Real.sinh (r / k) = Real.sinh (r / k) / (1 / k) := by field_simp

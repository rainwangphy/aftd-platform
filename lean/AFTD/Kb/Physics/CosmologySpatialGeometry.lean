import AFTD.Prelude

/-!
# Cosmology.SpatialGeometry

Topic: cosmology   Node: cc6a339a9ab9

Provenance: formalization of a published result. Source: Physlib, `Cosmology.SpatialGeometry`. Lean proof by Luis Gabriel C. Bariuan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Cosmology/FLRW/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The inductive type with three constructors: - `Spherical (k : ℝ)` - `Flat` - `Saddle (k : ℝ)`
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
open scoped Topology in
/-- The inductive type with three constructors: - `Spherical (k : ℝ)` - `Flat` - `Saddle (k : ℝ)` -/
inductive Cosmology.SpatialGeometry : Type where
  | Spherical (k : ℝ) (h : k < 0)
  | Flat
  | Saddle (k : ℝ) (h : k > 0)

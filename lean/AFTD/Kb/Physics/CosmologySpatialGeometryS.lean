import AFTD.Prelude
import AFTD.Kb.Physics.CosmologySpatialGeometry

/-!
# Cosmology.SpatialGeometry.S

Topic: cosmology   Node: 280c00f2905b

Provenance: formalization of a published result. Source: Physlib, `Cosmology.SpatialGeometry.S`. Lean proof by Luis Gabriel C. Bariuan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Cosmology/FLRW/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For `s` corresponding to - `Spherical k`, `S s r = k * sin (r / k)` - `Flat`, `S s r = r`, - `Saddle k`, `S s r = k * sinh (r / k)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
open scoped Topology in
/-- For `s` corresponding to - `Spherical k`, `S s r = k * sin (r / k)` - `Flat`, `S s r = r`, - `Saddle k`, `S s r = k * sinh (r / k)`. -/
noncomputable def Cosmology.SpatialGeometry.S (s : SpatialGeometry) : ℝ → ℝ :=
  fun r =>
    match s with
    | SpatialGeometry.Spherical k _ => k * Real.sin (r / k)
    | SpatialGeometry.Flat => r
    | SpatialGeometry.Saddle k _ => k * Real.sinh (r / k)

import AFTD.Prelude
import AFTD.Kb.Physics.CosmologySpatialGeometryTendstoSinRxOverX

/-!
# Cosmology.SpatialGeometry.limit_S_sphere

Topic: cosmology   Node: 1d58086fe565

Provenance: formalization of a published result. Source: Physlib, `Cosmology.SpatialGeometry.limit_S_sphere`. Lean proof by Luis Gabriel C. Bariuan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Cosmology/FLRW/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cosmology.SpatialGeometry.limit_S_sphere
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
open scoped Topology in
lemma Cosmology.SpatialGeometry.limit_S_sphere(r : ℝ) :
    Tendsto (fun k : ℝ => k * Real.sin (r / k)) atTop (𝓝 r) := by
  have hg : Tendsto (fun k : ℝ => 1 / k) atTop (𝓝[≠] 0) := by
    simpa only [one_div] using tendsto_inv_atTop_nhdsGT_zero.mono_right (nhdsGT_le_nhdsNE 0)
  exact ((tendsto_sin_rx_over_x r).comp hg).congr fun k => by
    simp only [Function.comp_apply, mul_one_div, div_div_eq_mul_div, div_one, mul_comm]

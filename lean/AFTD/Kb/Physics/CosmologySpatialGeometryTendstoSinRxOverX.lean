import AFTD.Prelude

/-!
# Cosmology.SpatialGeometry.tendsto_sin_rx_over_x

Topic: cosmology   Node: c9696cf073b4

Provenance: formalization of a published result. Source: Physlib, `Cosmology.SpatialGeometry.tendsto_sin_rx_over_x`. Lean proof by Luis Gabriel C. Bariuan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Cosmology/FLRW/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

First, show that limit of `sin(r * x) / x` is r at the limit x goes to zero. Then the next theorem will address the rewrite using Filter.Tendsto.comp
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter in
open scoped Topology in
/-- First, show that limit of `sin(r * x) / x` is r at the limit x goes to zero. Then the next theorem will address the rewrite using Filter.Tendsto.comp -/
lemma Cosmology.SpatialGeometry.tendsto_sin_rx_over_x (r : ℝ) :
    Tendsto (fun x : ℝ => Real.sin (r * x) / x) (𝓝[≠] 0) (𝓝 r) := by
  simpa [div_eq_inv_mul] using HasDerivAt.tendsto_slope_zero
    (HasDerivAt.sin (HasDerivAt.const_mul r (hasDerivAt_id 0)))

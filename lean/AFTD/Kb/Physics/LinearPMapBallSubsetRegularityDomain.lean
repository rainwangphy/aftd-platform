import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapIsLowerBound
import AFTD.Kb.Physics.LinearPMapRegularityDomain

/-!
# LinearPMap.ball_subset_regularityDomain

Topic: quantum_mechanics   Node: b0fd83417d19

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.ball_subset_regularityDomain`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/SpectralTheory/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The regularity domain of `T` contains open balls with radii controlled by the lower bounds.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
open Submodule in
open Metric in
open InnerProductSpace in
open Complex in
open ComplexConjugate in
open Set in
open Pointwise in
/-- The regularity domain of `T` contains open balls with radii controlled by the lower bounds. -/
lemma LinearPMap.ball_subset_regularityDomain
    {T : H →ₗ.[ℂ] H} {z : ℂ} {c : ℝ} (h : IsLowerBound T z c) : ball z c ⊆ T.regularityDomain := by
  intro z' hzc
  refine ⟨c - ‖z - z'‖, by simp_all [dist_eq, norm_sub_rev], fun x ↦ ?_⟩
  calc
    _ = c * ‖x‖ - ‖(z - z') • x‖ := by simp [sub_mul, norm_smul]
    _ ≤ ‖T x - z • x‖ - ‖(z - z') • x‖ := by linarith [h x]
    _ ≤ ‖T x - z • x + (z - z') • x‖ := norm_sub_le_norm_add _ _
    _ = ‖T x - z' • x‖ := by simp [sub_smul]

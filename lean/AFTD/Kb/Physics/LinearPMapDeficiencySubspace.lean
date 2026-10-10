import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapResolvent
import AFTD.Kb.Physics.LinearPMapInstMonoid
import AFTD.Kb.Physics.UnitaryOneParameterGroupGenerator

/-!
# LinearPMap.deficiencySubspace

Topic: quantum_mechanics   Node: 0376dc2c6f90

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.deficiencySubspace`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/SpectralTheory/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For a partial linear map `T` and any complex number `z`, the closed submodule which is orthogonal to the range of `T - z • 1`. `T.defectNumber z` is defined as the rank of this subspace.
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
/-- For a partial linear map `T` and any complex number `z`, the closed submodule which is orthogonal to the range of `T - z • 1`. `T.defectNumber z` is defined as the rank of this subspace. -/
noncomputable def LinearPMap.deficiencySubspace (T : H →ₗ.[ℂ] H) (z : ℂ) : ClosedSubmodule ℂ H :=
  ⟨(T - z • 1).toFun.rangeᗮ, isClosed_orthogonal _⟩

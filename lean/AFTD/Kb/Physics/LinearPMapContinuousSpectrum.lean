import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapResolvent
import AFTD.Kb.Physics.LinearPMapInstMonoid
import AFTD.Kb.Physics.LinearPMapDeficiencySubspace
import AFTD.Kb.Physics.UnitaryOneParameterGroupGenerator

/-!
# LinearPMap.continuousSpectrum

Topic: quantum_mechanics   Node: a4f6df73f2a2

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.continuousSpectrum`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/SpectralTheory/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The continuous spectrum, `σᶜ`, of a partial linear map. A complex number `z` is in `σᶜ T` iff the range of `T - z • 1` is not closed.
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
/-- The continuous spectrum, `σᶜ`, of a partial linear map. A complex number `z` is in `σᶜ T` iff the range of `T - z • 1` is not closed. -/
noncomputable def LinearPMap.continuousSpectrum (T : H →ₗ.[ℂ] H) : Set ℂ :=
  {z : ℂ | ¬_root_.IsClosed ((T - z • 1).toFun.range : Set H)}

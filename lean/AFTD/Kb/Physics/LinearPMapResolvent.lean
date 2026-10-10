import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapInstMonoid
import AFTD.Kb.Physics.UnitaryOneParameterGroupGenerator

/-!
# LinearPMap.resolvent

Topic: quantum_mechanics   Node: 7459dfe8ed78

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.resolvent`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/SpectralTheory/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The resolvent, `(T - z • 1)⁻¹`.
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
/-- The resolvent, `(T - z • 1)⁻¹`. -/
noncomputable abbrev LinearPMap.resolvent (T : H →ₗ.[ℂ] H) (z : ℂ) : H →ₗ.[ℂ] H := (T - z • 1).inverse

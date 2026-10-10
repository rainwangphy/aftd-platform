import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapDeficiencySubspace

/-!
# LinearPMap.defectNumber

Topic: quantum_mechanics   Node: 781b90564b83

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.defectNumber`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/SpectralTheory/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The rank of `T.deficiencySubspace z = (T - z • 1).rangeᗮ`.
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
/-- The rank of `T.deficiencySubspace z = (T - z • 1).rangeᗮ`. -/
noncomputable def LinearPMap.defectNumber (T : H →ₗ.[ℂ] H) (z : ℂ) : Cardinal := Module.rank ℂ (T.deficiencySubspace z)

import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapDeficiencySubspace
import AFTD.Kb.Physics.LinearPMapInstMonoid

/-!
# LinearPMap.deficiencySubspace_coe

Topic: quantum_mechanics   Node: 92ab014e80a2

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.deficiencySubspace_coe`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/SpectralTheory/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.deficiencySubspace_coe
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
@[simp]
lemma LinearPMap.deficiencySubspace_coe (T : H →ₗ.[ℂ] H) (z : ℂ) :
    T.deficiencySubspace z = (T - z • 1).toFun.rangeᗮ := rfl

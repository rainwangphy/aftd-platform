import AFTD.Prelude
import AFTD.Kb.Physics.StandardModelHiggsVec

/-!
# StandardModel.HiggsVec.orthonormBasis

Topic: quantum_field_theory   Node: 230d4c282e4c

Provenance: formalization of a published result. Source: Physlib, `StandardModel.HiggsVec.orthonormBasis`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/HiggsBoson/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An orthonormal basis of `HiggsVec`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold in
open Matrix in
open Complex in
open ComplexConjugate in
/-- An orthonormal basis of `HiggsVec`. -/
noncomputable def StandardModel.HiggsVec.orthonormBasis : OrthonormalBasis (Fin 2) ℂ HiggsVec :=
  EuclideanSpace.basisFun (Fin 2) ℂ

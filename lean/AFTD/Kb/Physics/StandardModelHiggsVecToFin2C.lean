import AFTD.Prelude
import AFTD.Kb.Physics.StandardModelHiggsVec

/-!
# StandardModel.HiggsVec.toFin2ℂ

Topic: quantum_field_theory   Node: 20a22d91dcc7

Provenance: formalization of a published result. Source: Physlib, `StandardModel.HiggsVec.toFin2ℂ`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/HiggsBoson/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The continuous linear map from the vector space `HiggsVec` to `(Fin 2 → ℂ)` achieved by casting vectors.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold in
open Matrix in
open Complex in
open ComplexConjugate in
/-- The continuous linear map from the vector space `HiggsVec` to `(Fin 2 → ℂ)` achieved by casting vectors. -/
noncomputable def StandardModel.HiggsVec.toFin2ℂ : HiggsVec →L[ℝ] (Fin 2 → ℂ) where
  toFun x := x
  map_add' x y := rfl
  map_smul' a x := rfl

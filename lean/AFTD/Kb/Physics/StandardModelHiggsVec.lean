import AFTD.Prelude

/-!
# StandardModel.HiggsVec

Topic: quantum_field_theory   Node: cefaedee1109

Provenance: formalization of a published result. Source: Physlib, `StandardModel.HiggsVec`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/HiggsBoson/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The vector space `HiggsVec` is defined to be the complex Euclidean space of dimension 2. For a given spacetime point a Higgs field gives a value in `HiggsVec`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold in
open Matrix in
open Complex in
open ComplexConjugate in
/-- The vector space `HiggsVec` is defined to be the complex Euclidean space of dimension 2. For a given spacetime point a Higgs field gives a value in `HiggsVec`. -/
noncomputable abbrev StandardModel.HiggsVec := EuclideanSpace ℂ (Fin 2)

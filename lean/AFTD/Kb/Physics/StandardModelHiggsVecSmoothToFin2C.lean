import AFTD.Prelude
import AFTD.Kb.Physics.StandardModelHiggsVec
import AFTD.Kb.Physics.StandardModelHiggsVecToFin2C

/-!
# StandardModel.HiggsVec.smooth_toFin2ℂ

Topic: quantum_field_theory   Node: c7e269398923

Provenance: formalization of a published result. Source: Physlib, `StandardModel.HiggsVec.smooth_toFin2ℂ`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/HiggsBoson/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The map `toFin2ℂ` is smooth.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold in
open Matrix in
open Complex in
open ComplexConjugate in
/-- The map `toFin2ℂ` is smooth. -/
lemma StandardModel.HiggsVec.smooth_toFin2ℂ : ContMDiff 𝓘(ℝ, HiggsVec) 𝓘(ℝ, Fin 2 → ℂ) ⊤ toFin2ℂ :=
  toFin2ℂ.contMDiff

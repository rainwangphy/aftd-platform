import AFTD.Prelude
import AFTD.Kb.Physics.StandardModelHiggsVec

/-!
# StandardModel.HiggsVec.ofReal

Topic: quantum_field_theory   Node: 2c1d19a76b15

Provenance: formalization of a published result. Source: Physlib, `StandardModel.HiggsVec.ofReal`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/HiggsBoson/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Generating a Higgs vector from a real number, such that the norm-squared of that Higgs vector is the given real number.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold in
open Matrix in
open Complex in
open ComplexConjugate in
/-- Generating a Higgs vector from a real number, such that the norm-squared of that Higgs vector is the given real number. -/
noncomputable def StandardModel.HiggsVec.ofReal (a : ℝ) : HiggsVec :=
  !₂[Real.sqrt a, 0]

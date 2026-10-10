import AFTD.Prelude

/-!
# StandardModel.HiggsField.Potential

Topic: quantum_field_theory   Node: 3c1b17ac3ce1

Provenance: formalization of a published result. Source: Physlib, `StandardModel.HiggsField.Potential`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/HiggsBoson/Potential.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The structure `Potential` is defined with two fields, `μ2` corresponding to the mass-squared of the Higgs boson, and `l` corresponding to the coefficient of the quartic term in the Higgs potential. Note that `l` is usually denoted `λ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold in
open Matrix in
open Complex in
open ComplexConjugate in
/-- The structure `Potential` is defined with two fields, `μ2` corresponding to the mass-squared of the Higgs boson, and `l` corresponding to the coefficient of the quartic term in the Higgs potential. Note that `l` is usually denoted `λ`. -/
structure StandardModel.HiggsField.Potential where
  /-- The mass-squared of the Higgs boson. -/
  μ2 : ℝ
  /-- The quartic coupling of the Higgs boson. Usually denoted λ. -/
  𝓵 : ℝ

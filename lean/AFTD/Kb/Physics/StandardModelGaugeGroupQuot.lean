import AFTD.Prelude

/-!
# StandardModel.GaugeGroupQuot

Topic: quantum_field_theory   Node: a66a09fd2c6d

Provenance: formalization of a published result. Source: Physlib, `StandardModel.GaugeGroupQuot`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Specifies the allowed quotients of `SU(3) x SU(2) x U(1)` which give a valid gauge group of the Standard Model.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold in
open Matrix in
open Complex in
open ComplexConjugate in
set_option backward.isDefEq.respectTransparency false in
/-- Specifies the allowed quotients of `SU(3) x SU(2) x U(1)` which give a valid gauge group of the Standard Model. -/
inductive StandardModel.GaugeGroupQuot : Type
  /-- The element of `GaugeGroupQuot` corresponding to the quotient of the full SM gauge group
    by the sub-group `ℤ₆`. -/ | ℤ₆ : GaugeGroupQuot
  /-- The element of `GaugeGroupQuot` corresponding to the quotient of the full SM gauge group
    by the sub-group `ℤ₂`. -/
  | ℤ₂ : GaugeGroupQuot
  /-- The element of `GaugeGroupQuot` corresponding to the quotient of the full SM gauge group
    by the sub-group `ℤ₃`. -/
  | ℤ₃ : GaugeGroupQuot
  /-- The element of `GaugeGroupQuot` corresponding to the full SM gauge group. -/
  | I : GaugeGroupQuot
deriving Fintype, DecidableEq

import AFTD.Prelude

/-!
# StandardModel.GaugeGroupI

Topic: quantum_field_theory   Node: 6d813df747b8

Provenance: formalization of a published result. Source: Physlib, `StandardModel.GaugeGroupI`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The global gauge group of the Standard Model with no discrete quotients. The `I` in the Name is an indication of the statement that this has no discrete quotients.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold in
open Matrix in
open Complex in
open ComplexConjugate in
/-- The global gauge group of the Standard Model with no discrete quotients. The `I` in the Name is an indication of the statement that this has no discrete quotients. -/
abbrev StandardModel.GaugeGroupI : Type :=
  specialUnitaryGroup (Fin 3) ℂ × specialUnitaryGroup (Fin 2) ℂ × unitary ℂ

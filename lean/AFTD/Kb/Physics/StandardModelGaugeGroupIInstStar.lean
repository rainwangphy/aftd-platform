import AFTD.Prelude
import AFTD.Kb.Physics.StandardModelGaugeGroupI

/-!
# StandardModel.GaugeGroupI.instStar

Topic: quantum_field_theory   Node: 2e197e636a89

Provenance: formalization of a published result. Source: Physlib, `StandardModel.GaugeGroupI.instStar`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

StandardModel.GaugeGroupI.instStar
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold in
open Matrix in
open Complex in
open ComplexConjugate in
instance StandardModel.GaugeGroupI.instStar : Star GaugeGroupI where
  star g := (star g.1, star g.2.1, star g.2.2)

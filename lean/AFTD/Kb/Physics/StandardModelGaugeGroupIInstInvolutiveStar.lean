import AFTD.Prelude
import AFTD.Kb.Physics.StandardModelGaugeGroupI
import AFTD.Kb.Physics.StandardModelGaugeGroupIInstStar
import AFTD.Kb.Physics.StandardModelGaugeGroupIExt
import AFTD.Kb.Physics.StandardModelGaugeGroupIToSU3
import AFTD.Kb.Physics.StandardModelGaugeGroupIToSU2
import AFTD.Kb.Physics.StandardModelGaugeGroupIToU1
import AFTD.Kb.Physics.StandardModelGaugeGroupIStarToSU3
import AFTD.Kb.Physics.StandardModelGaugeGroupIStarToSU2
import AFTD.Kb.Physics.StandardModelGaugeGroupIStarToU1

/-!
# StandardModel.GaugeGroupI.instInvolutiveStar

Topic: quantum_field_theory   Node: b7df3278d91c

Provenance: formalization of a published result. Source: Physlib, `StandardModel.GaugeGroupI.instInvolutiveStar`. Lean proof by Nikolai Kashcheev, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/StandardModel/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

StandardModel.GaugeGroupI.instInvolutiveStar
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Manifold in
open Matrix in
open Complex in
open ComplexConjugate in
instance StandardModel.GaugeGroupI.instInvolutiveStar : InvolutiveStar GaugeGroupI where
  star_involutive g := by
    ext1 <;> simp

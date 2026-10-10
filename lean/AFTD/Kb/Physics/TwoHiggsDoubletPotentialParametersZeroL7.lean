import AFTD.Prelude
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParameters
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParametersInstZero
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParametersZeroM112
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParametersZeroM222
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParametersZeroM122
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParametersZeroL1
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParametersZeroL2
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParametersZeroL3
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParametersZeroL4
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParametersZeroL5
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParametersZeroL6

/-!
# TwoHiggsDoublet.PotentialParameters.zero_𝓵₇

Topic: quantum_field_theory   Node: 6aad4654ffbd

Provenance: formalization of a published result. Source: Physlib, `TwoHiggsDoublet.PotentialParameters.zero_𝓵₇`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/TwoHDM/Potential.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TwoHiggsDoublet.PotentialParameters.zero_𝓵₇
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace in
@[simp] lemma TwoHiggsDoublet.PotentialParameters.zero_𝓵₇ : (0 : PotentialParameters).𝓵₇ = 0 := rfl

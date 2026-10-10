import AFTD.Prelude
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParameters
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParametersInstZero
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParametersZeroM112
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParametersZeroM222

/-!
# TwoHiggsDoublet.PotentialParameters.zero_m₁₂2

Topic: quantum_field_theory   Node: b6b9dd620c54

Provenance: formalization of a published result. Source: Physlib, `TwoHiggsDoublet.PotentialParameters.zero_m₁₂2`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/TwoHDM/Potential.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TwoHiggsDoublet.PotentialParameters.zero_m₁₂2
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace in
@[simp] lemma TwoHiggsDoublet.PotentialParameters.zero_m₁₂2 : (0 : PotentialParameters).m₁₂2 = 0 := rfl

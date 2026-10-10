import AFTD.Prelude
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParameters
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParametersInstZero

/-!
# TwoHiggsDoublet.PotentialParameters.zero_m₁₁2

Topic: quantum_field_theory   Node: 06fa75a43b68

Provenance: formalization of a published result. Source: Physlib, `TwoHiggsDoublet.PotentialParameters.zero_m₁₁2`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/TwoHDM/Potential.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TwoHiggsDoublet.PotentialParameters.zero_m₁₁2
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace in
@[simp] lemma TwoHiggsDoublet.PotentialParameters.zero_m₁₁2 : (0 : PotentialParameters).m₁₁2 = 0 := rfl

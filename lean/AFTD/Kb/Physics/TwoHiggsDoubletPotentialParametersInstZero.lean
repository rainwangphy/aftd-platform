import AFTD.Prelude
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParameters

/-!
# TwoHiggsDoublet.PotentialParameters.instZero

Topic: quantum_field_theory   Node: 0cc3d8478407

Provenance: formalization of a published result. Source: Physlib, `TwoHiggsDoublet.PotentialParameters.instZero`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/TwoHDM/Potential.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

TwoHiggsDoublet.PotentialParameters.instZero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace in
instance TwoHiggsDoublet.PotentialParameters.instZero : Zero PotentialParameters where
  zero :=
    { m₁₁2 := 0
      m₂₂2 := 0
      m₁₂2 := 0
      𝓵₁ := 0
      𝓵₂ := 0
      𝓵₃ := 0
      𝓵₄ := 0
      𝓵₅ := 0
      𝓵₆ := 0
      𝓵₇ := 0 }

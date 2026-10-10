import AFTD.Prelude
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParameters
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParametersZeroM112
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParametersZeroM222
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParametersZeroM122
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParametersZeroL1
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParametersZeroL2
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParametersZeroL3
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParametersZeroL4
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParametersZeroL5
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParametersZeroL6
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParametersZeroL7
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParametersInstZero
import AFTD.Kb.Physics.PauliMatrixPauliMatrix

/-!
# TwoHiggsDoublet.PotentialParameters.ξ

Topic: quantum_field_theory   Node: d9a59f09ad92

Provenance: formalization of a published result. Source: Physlib, `TwoHiggsDoublet.PotentialParameters.ξ`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/TwoHDM/Potential.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A reparameterization of the parameters of the quadratic terms of the potential for use with the gramVector.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace in
/-- A reparameterization of the parameters of the quadratic terms of the potential for use with the gramVector. -/
noncomputable def TwoHiggsDoublet.PotentialParameters.ξ (P : PotentialParameters) (μ : Fin 1 ⊕ Fin 3) : ℝ :=
  match μ with
  | .inl 0 => (P.m₁₁2 + P.m₂₂2) / 2
  | .inr 0 => -Complex.re P.m₁₂2
  | .inr 1 => Complex.im P.m₁₂2
  | .inr 2 => (P.m₁₁2 - P.m₂₂2) / 2

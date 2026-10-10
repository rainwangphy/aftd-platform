import AFTD.Prelude
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParameters
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParametersXi
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
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParametersXiZero
import AFTD.Kb.Physics.TwoHiggsDoubletPotentialParametersInstZero
import AFTD.Kb.GameTheoryEconomics.PcxTheta

/-!
# TwoHiggsDoublet.PotentialParameters.η

Topic: quantum_field_theory   Node: fbe2d125e51f

Provenance: formalization of a published result. Source: Physlib, `TwoHiggsDoublet.PotentialParameters.η`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/BeyondTheStandardModel/TwoHDM/Potential.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A reparameterization of the parameters of the quartic terms of the potential for use with the gramVector.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open InnerProductSpace in
/-- A reparameterization of the parameters of the quartic terms of the potential for use with the gramVector. -/
noncomputable def TwoHiggsDoublet.PotentialParameters.η (P : PotentialParameters) : Fin 1 ⊕ Fin 3 → Fin 1 ⊕ Fin 3 → ℝ
  | .inl 0, .inl 0 => (P.𝓵₁ + P.𝓵₂ + 2 * P.𝓵₃) / 8
  | .inl 0, .inr 0 => (P.𝓵₆.re + P.𝓵₇.re) / 4
  | .inl 0, .inr 1 => - (P.𝓵₆.im + P.𝓵₇.im) / 4
  | .inl 0, .inr 2 => (P.𝓵₁ - P.𝓵₂) / 8
  | .inr 0, .inl 0 => (P.𝓵₆.re + P.𝓵₇.re) / 4
  | .inr 1, .inl 0 => -(P.𝓵₆.im + P.𝓵₇.im) / 4
  | .inr 2, .inl 0 => (P.𝓵₁ - P.𝓵₂) / 8
  | .inr 0, .inr 0 => (P.𝓵₅.re + P.𝓵₄) / 4
  | .inr 1, .inr 1 => (P.𝓵₄ - P.𝓵₅.re) / 4
  | .inr 2, .inr 2 => (P.𝓵₁ + P.𝓵₂ - 2 * P.𝓵₃) / 8
  | .inr 0, .inr 1 => - P.𝓵₅.im / 4
  | .inr 2, .inr 0 => (P.𝓵₆.re - P.𝓵₇.re) / 4
  | .inr 2, .inr 1 => (P.𝓵₇.im - P.𝓵₆.im) / 4
  | .inr 1, .inr 0 => - P.𝓵₅.im / 4
  | .inr 0, .inr 2 => (P.𝓵₆.re - P.𝓵₇.re) / 4
  | .inr 1, .inr 2 => (P.𝓵₇.im - P.𝓵₆.im) / 4

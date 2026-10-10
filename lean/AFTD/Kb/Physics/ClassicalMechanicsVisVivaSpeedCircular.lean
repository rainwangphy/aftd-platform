import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsVisViva
import AFTD.Kb.Physics.ClassicalMechanicsVisVivaConfigurationSpace

/-!
# ClassicalMechanics.VisViva.speedCircular

Topic: classical_mechanics   Node: 1d4e595d3be5

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.VisViva.speedCircular`. Lean proof by Hannah Dawe, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/OrbitalMechanics/VisViva.lean (Copyright (c) 2026 Hannah Dawe. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The orbital speed required for a circular orbit at radius `r`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The orbital speed required for a circular orbit at radius `r`. -/
noncomputable def ClassicalMechanics.VisViva.speedCircular (sys : VisViva) (cfg : ConfigurationSpace) : ℝ :=
  Real.sqrt (sys.G * sys.M / cfg.r)

import AFTD.Prelude
import AFTD.Kb.Physics.ClassicalMechanicsVisViva
import AFTD.Kb.Physics.ClassicalMechanicsVisVivaConfigurationSpace
import AFTD.Kb.Physics.ClassicalMechanicsVisVivaSpeedCircular

/-!
# ClassicalMechanics.VisViva.speedCircular_sq

Topic: classical_mechanics   Node: 798967ff4c8d

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.VisViva.speedCircular_sq`. Lean proof by Hannah Dawe, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/OrbitalMechanics/VisViva.lean (Copyright (c) 2026 Hannah Dawe. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lemma: the square of the circular orbit speed equals G M / r.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Lemma: the square of the circular orbit speed equals G M / r. -/
lemma ClassicalMechanics.VisViva.speedCircular_sq (sys : VisViva) (cfg : ConfigurationSpace) (hr : 0 < cfg.r) (hG : 0 < sys.G)
    (hM : 0 < sys.M) :
    (speedCircular sys cfg)^2 = sys.G * sys.M / cfg.r :=
  Real.sq_sqrt (by positivity)

import AFTD.Prelude

/-!
# ClassicalMechanics.FreeParticle

Topic: classical_mechanics   Node: 0fc8ac378574

Provenance: formalization of a published result. Source: Physlib, `ClassicalMechanics.FreeParticle`. Lean proof by Pranav Magdum, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ClassicalMechanics/FreeParticle/Basic.lean (Copyright (c) 2026 Pranav Magdum. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A classical free particle with positive mass. A free particle is a mechanical system evolving in the absence of external forces. The dynamics are therefore entirely determined by Newton's second law with zero force. The only parameter of the system is the particle mass. The assumption that the mass is strictly positive is physically natural and is used throughout the development when simplifying the equation of motion.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A classical free particle with positive mass. A free particle is a mechanical system evolving in the absence of external forces. The dynamics are therefore entirely determined by Newton's second law with zero force. The only parameter of the system is the particle mass. The assumption that the mass is strictly positive is physically natural and is used throughout the development when simplifying the equation of motion. -/
structure ClassicalMechanics.FreeParticle where
  /--
  The mass of the free particle.

  This parameter determines the inertial response of the particle in
  Newton's second law.
  -/
  mass : ℝ
  mass_pos : 0 < mass

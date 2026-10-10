import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsFreeParticle
import AFTD.Kb.Physics.QuantumMechanicsFreeParticleMPos
import AFTD.Kb.Physics.QuantumMechanicsFreeParticleMNonneg

/-!
# QuantumMechanics.FreeParticle.m_ne_zero

Topic: quantum_mechanics   Node: 5378319d08b2

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.FreeParticle.m_ne_zero`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/FreeParticle/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

QuantumMechanics.FreeParticle.m_ne_zero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open QuantumMechanics in
variable {d : ℕ} (Q : FreeParticle d) in
@[simp]
lemma QuantumMechanics.FreeParticle.m_ne_zero : Q.m ≠ 0 := Q.hm.ne'

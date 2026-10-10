import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsFreeParticle

/-!
# QuantumMechanics.FreeParticle.m_pos

Topic: quantum_mechanics   Node: a040e76d369b

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.FreeParticle.m_pos`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/FreeParticle/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

QuantumMechanics.FreeParticle.m_pos
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open QuantumMechanics in
variable {d : ℕ} (Q : FreeParticle d) in
@[simp]
lemma QuantumMechanics.FreeParticle.m_pos : 0 < Q.m := Q.hm

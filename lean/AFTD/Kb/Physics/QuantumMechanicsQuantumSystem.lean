import AFTD.Prelude

/-!
# QuantumMechanics.QuantumSystem

Topic: quantum_mechanics   Node: 19769d7db319

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.QuantumSystem`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/QuantumSystem/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A quantum system is identified by its Hilbert space and self-adjoint Hamiltonian operator.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
/-- A quantum system is identified by its Hilbert space and self-adjoint Hamiltonian operator. -/
structure QuantumMechanics.QuantumSystem where
  /-- The complex Hilbert space. -/
  HS : Type*
  /-- The Hilbert space is a normed, commutative group. -/
  [instNormed : NormedAddCommGroup HS]
  /-- The Hilbert space is a complex inner product space. -/
  [instInner : InnerProductSpace ℂ HS]
  /-- The Hilbert space is complete. -/
  [instComplete : CompleteSpace HS]
  /-- The self-adjoint Hamiltonian operator. -/
  ℋ : HS →ₗ.[ℂ] HS
  ℋ_self_adjoint : IsSelfAdjoint ℋ

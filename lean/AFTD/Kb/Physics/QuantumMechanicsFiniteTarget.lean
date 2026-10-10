import AFTD.Prelude

/-!
# QuantumMechanics.FiniteTarget

Topic: quantum_mechanics   Node: fd8915f0a7bf

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.FiniteTarget`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/FiniteTarget.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A finite-dimensional quantum system with a self-adjoint Hamiltonian.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
/-- A finite-dimensional quantum system with a self-adjoint Hamiltonian. -/
structure QuantumMechanics.FiniteTarget (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [FiniteDimensional ℂ H] (n : ℕ) where
  /-- The Hilbert space has dimension `n`. -/
  hdim: Module.finrank ℂ H = n
  /-- The Hamiltonian. -/
  Ham : H →L[ℂ] H
  /-- The Hamiltonian is self-adjoint. -/
  Ham_selfAdjoint: IsSelfAdjoint Ham

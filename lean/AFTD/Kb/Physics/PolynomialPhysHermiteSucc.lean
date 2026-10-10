import AFTD.Prelude
import AFTD.Kb.Physics.PolynomialPhysHermite

/-!
# Polynomial.physHermite_succ

Topic: classical_mechanics   Node: f8147b4cbf0b

Provenance: formalization of a published result. Source: Physlib, `Polynomial.physHermite_succ`. Lean proof by Gregory J. Loges, Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/SpecialFunctions/PhysHermite.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The defining recursion `physHermite (n + 1) = (2x - d/dx) (physHermite n)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Nat in
/-- The defining recursion `physHermite (n + 1) = (2x - d/dx) (physHermite n)`. -/
lemma Polynomial.physHermite_succ (n : ℕ) :
    physHermite (n + 1) = 2 • X * physHermite n - derivative (physHermite n) := by
  simp [physHermite]

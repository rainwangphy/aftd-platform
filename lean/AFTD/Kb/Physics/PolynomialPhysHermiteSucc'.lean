import AFTD.Prelude
import AFTD.Kb.Physics.PolynomialPhysHermite
import AFTD.Kb.Physics.PolynomialPhysHermiteSucc
import AFTD.Kb.Physics.PolynomialDerivativePhysHermite
import AFTD.Kb.Physics.PolynomialPhysHermiteZero
import AFTD.Kb.Physics.PolynomialPhysHermiteOne

/-!
# Polynomial.physHermite_succ'

Topic: classical_mechanics   Node: 0136290c8737

Provenance: formalization of a published result. Source: Physlib, `Polynomial.physHermite_succ'`. Lean proof by Gregory J. Loges, Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/SpecialFunctions/PhysHermite.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Polynomial.physHermite_succ'
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Nat in
lemma Polynomial.physHermite_succ' (n : ℕ) :
    physHermite (n + 1) = 2 • X * physHermite n - 2 * n • physHermite (n - 1) := by
  rw [physHermite_succ, derivative_physHermite]

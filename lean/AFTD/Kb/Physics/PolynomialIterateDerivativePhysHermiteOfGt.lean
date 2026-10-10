import AFTD.Prelude
import AFTD.Kb.Physics.PolynomialPhysHermite
import AFTD.Kb.Physics.PolynomialNatDegreePhysHermite
import AFTD.Kb.Physics.PolynomialPhysHermiteZero
import AFTD.Kb.Physics.PolynomialPhysHermiteOne
import AFTD.Kb.Physics.PolynomialCoeffPhysHermiteSelf
import AFTD.Kb.Physics.PolynomialDegreePhysHermite
import AFTD.Kb.Physics.PolynomialPhysHermiteLeadingCoeff
import AFTD.Kb.Physics.PolynomialPhysHermiteNeZero

/-!
# Polynomial.iterate_derivative_physHermite_of_gt

Topic: classical_mechanics   Node: 653ab51ae763

Provenance: formalization of a published result. Source: Physlib, `Polynomial.iterate_derivative_physHermite_of_gt`. Lean proof by Gregory J. Loges, Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/SpecialFunctions/PhysHermite.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Polynomial.iterate_derivative_physHermite_of_gt
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Nat in
lemma Polynomial.iterate_derivative_physHermite_of_gt {n m : ℕ} (h : n < m) :
    derivative^[m] (physHermite n) = 0 :=
  iterate_derivative_eq_zero (by simpa using h)

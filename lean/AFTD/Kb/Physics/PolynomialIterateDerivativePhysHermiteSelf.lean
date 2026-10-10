import AFTD.Prelude
import AFTD.Kb.Physics.PolynomialPhysHermite
import AFTD.Kb.Physics.PolynomialCoeffPhysHermiteSelf
import AFTD.Kb.Physics.PolynomialCoeffPhysHermiteOfLt
import AFTD.Kb.Physics.PolynomialPhysHermiteZero
import AFTD.Kb.Physics.PolynomialPhysHermiteOne
import AFTD.Kb.Physics.PolynomialDegreePhysHermite
import AFTD.Kb.Physics.PolynomialNatDegreePhysHermite
import AFTD.Kb.Physics.PolynomialPhysHermiteLeadingCoeff
import AFTD.Kb.Physics.PolynomialPhysHermiteNeZero
import AFTD.Kb.Tcs.CslibOmegaSequenceTakeSucc'

/-!
# Polynomial.iterate_derivative_physHermite_self

Topic: classical_mechanics   Node: e18bca83e5fd

Provenance: formalization of a published result. Source: Physlib, `Polynomial.iterate_derivative_physHermite_self`. Lean proof by Gregory J. Loges, Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/SpecialFunctions/PhysHermite.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Polynomial.iterate_derivative_physHermite_self
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Nat in
@[simp]
lemma Polynomial.iterate_derivative_physHermite_self (n : ℕ) :
    derivative^[n] (physHermite n) = C (n ! * 2 ^ n : ℤ) := by
  ext m
  rw [Polynomial.coeff_iterate_derivative]
  match m with
  | 0 =>
    rw [Polynomial.coeff_C_zero]
    simp [Nat.descFactorial_self]
  | m + 1 =>
    rw [coeff_physHermite_of_lt (by omega), Polynomial.coeff_C_of_ne_zero (by omega), smul_zero]

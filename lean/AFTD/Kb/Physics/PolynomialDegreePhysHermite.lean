import AFTD.Prelude
import AFTD.Kb.Physics.PolynomialPhysHermite
import AFTD.Kb.Physics.PolynomialCoeffPhysHermiteOfLt
import AFTD.Kb.Physics.PolynomialCoeffPhysHermiteSelf
import AFTD.Kb.Physics.PolynomialPhysHermiteZero
import AFTD.Kb.Physics.PolynomialPhysHermiteOne

/-!
# Polynomial.degree_physHermite

Topic: classical_mechanics   Node: c328960cc100

Provenance: formalization of a published result. Source: Physlib, `Polynomial.degree_physHermite`. Lean proof by Gregory J. Loges, Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/SpecialFunctions/PhysHermite.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Polynomial.degree_physHermite
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Nat in
@[simp]
lemma Polynomial.degree_physHermite (n : ℕ) : degree (physHermite n) = n := by
  refine degree_eq_of_le_of_coeff_ne_zero ?_ (by simp)
  simp_rw [degree_le_iff_coeff_zero, Nat.cast_lt]
  exact fun _ => coeff_physHermite_of_lt

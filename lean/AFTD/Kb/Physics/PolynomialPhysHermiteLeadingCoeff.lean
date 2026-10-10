import AFTD.Prelude
import AFTD.Kb.Physics.PolynomialPhysHermite
import AFTD.Kb.Physics.PolynomialNatDegreePhysHermite
import AFTD.Kb.Physics.PolynomialCoeffPhysHermiteSelf
import AFTD.Kb.Physics.PolynomialPhysHermiteZero
import AFTD.Kb.Physics.PolynomialPhysHermiteOne
import AFTD.Kb.Physics.PolynomialDegreePhysHermite

/-!
# Polynomial.physHermite_leadingCoeff

Topic: classical_mechanics   Node: 105f403c91dd

Provenance: formalization of a published result. Source: Physlib, `Polynomial.physHermite_leadingCoeff`. Lean proof by Gregory J. Loges, Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/SpecialFunctions/PhysHermite.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Polynomial.physHermite_leadingCoeff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Nat in
@[simp]
lemma Polynomial.physHermite_leadingCoeff (n : ℕ) : (physHermite n).leadingCoeff = 2 ^ n := by
  simp [leadingCoeff]

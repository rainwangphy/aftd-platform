import AFTD.Prelude
import AFTD.Kb.Physics.PolynomialPhysHermite
import AFTD.Kb.Physics.PolynomialPhysHermiteLeadingCoeff
import AFTD.Kb.Physics.PolynomialPhysHermiteZero
import AFTD.Kb.Physics.PolynomialPhysHermiteOne
import AFTD.Kb.Physics.PolynomialCoeffPhysHermiteSelf
import AFTD.Kb.Physics.PolynomialDegreePhysHermite
import AFTD.Kb.Physics.PolynomialNatDegreePhysHermite

/-!
# Polynomial.physHermite_ne_zero

Topic: classical_mechanics   Node: b66b32ed0387

Provenance: formalization of a published result. Source: Physlib, `Polynomial.physHermite_ne_zero`. Lean proof by Gregory J. Loges, Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/SpecialFunctions/PhysHermite.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Polynomial.physHermite_ne_zero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Nat in
@[simp]
lemma Polynomial.physHermite_ne_zero (n : ℕ) : physHermite n ≠ 0 :=
  leadingCoeff_ne_zero.mp (by simp)

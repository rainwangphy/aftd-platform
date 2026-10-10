import AFTD.Prelude
import AFTD.Kb.Physics.PolynomialPhysHermite
import AFTD.Kb.Physics.PolynomialDegreePhysHermite
import AFTD.Kb.Physics.PolynomialPhysHermiteZero
import AFTD.Kb.Physics.PolynomialPhysHermiteOne
import AFTD.Kb.Physics.PolynomialCoeffPhysHermiteSelf

/-!
# Polynomial.natDegree_physHermite

Topic: classical_mechanics   Node: e29f7d64f1dd

Provenance: formalization of a published result. Source: Physlib, `Polynomial.natDegree_physHermite`. Lean proof by Gregory J. Loges, Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/SpecialFunctions/PhysHermite.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Polynomial.natDegree_physHermite
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Nat in
@[simp]
lemma Polynomial.natDegree_physHermite (n : ℕ) : (physHermite n).natDegree = n :=
  natDegree_eq_of_degree_eq_some (degree_physHermite n)

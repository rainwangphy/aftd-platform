import AFTD.Prelude
import AFTD.Kb.Physics.PolynomialPhysHermite
import AFTD.Kb.Physics.PolynomialPhysHermiteSucc
import AFTD.Kb.Physics.PolynomialPhysHermiteZero

/-!
# Polynomial.physHermite_one

Topic: classical_mechanics   Node: 68a231e3db8e

Provenance: formalization of a published result. Source: Physlib, `Polynomial.physHermite_one`. Lean proof by Gregory J. Loges, Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/SpecialFunctions/PhysHermite.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Polynomial.physHermite_one
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Nat in
@[simp]
lemma Polynomial.physHermite_one : physHermite 1 = 2 * X := by simp [physHermite_succ]

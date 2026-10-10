import AFTD.Prelude
import AFTD.Kb.Physics.PolynomialPhysHermite
import AFTD.Kb.Physics.PolynomialDerivativePhysHermiteSucc
import AFTD.Kb.Physics.PolynomialPhysHermiteZero
import AFTD.Kb.Physics.PolynomialPhysHermiteOne
import AFTD.Kb.Tcs.CslibOmegaSequenceTakeSucc'

/-!
# Polynomial.derivative_physHermite

Topic: classical_mechanics   Node: 378b9132b232

Provenance: formalization of a published result. Source: Physlib, `Polynomial.derivative_physHermite`. Lean proof by Gregory J. Loges, Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/SpecialFunctions/PhysHermite.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Polynomial.derivative_physHermite
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Nat in
lemma Polynomial.derivative_physHermite : (n : ℕ) →
    derivative (physHermite n) = 2 * n • physHermite (n - 1)
  | 0 => by simp
  | n + 1 => by simp [derivative_physHermite_succ]

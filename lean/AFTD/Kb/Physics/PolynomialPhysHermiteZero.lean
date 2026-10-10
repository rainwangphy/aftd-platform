import AFTD.Prelude
import AFTD.Kb.Physics.PolynomialPhysHermite

/-!
# Polynomial.physHermite_zero

Topic: classical_mechanics   Node: 284d949b8b6e

Provenance: formalization of a published result. Source: Physlib, `Polynomial.physHermite_zero`. Lean proof by Gregory J. Loges, Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/SpecialFunctions/PhysHermite.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Polynomial.physHermite_zero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Nat in
@[simp]
lemma Polynomial.physHermite_zero : physHermite 0 = C 1 := rfl

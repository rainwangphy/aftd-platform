import AFTD.Prelude
import AFTD.Kb.Physics.PolynomialPhysHermite
import AFTD.Kb.Physics.PolynomialCoeffPhysHermiteSuccSucc
import AFTD.Kb.Physics.PolynomialCoeffPhysHermiteOfLt
import AFTD.Kb.Physics.PolynomialPhysHermiteZero
import AFTD.Kb.Physics.PolynomialPhysHermiteOne

/-!
# Polynomial.coeff_physHermite_self

Topic: classical_mechanics   Node: 020152b358bb

Provenance: formalization of a published result. Source: Physlib, `Polynomial.coeff_physHermite_self`. Lean proof by Gregory J. Loges, Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/SpecialFunctions/PhysHermite.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Polynomial.coeff_physHermite_self
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Nat in
@[simp]
lemma Polynomial.coeff_physHermite_self (n : ℕ) : coeff (physHermite n) n = 2 ^ n := by
  induction n with
  | zero => exact coeff_C
  | succ n ih =>
    rw [coeff_physHermite_succ_succ, ih, coeff_physHermite_of_lt (by omega), mul_zero, sub_zero,
      ← Int.pow_succ']

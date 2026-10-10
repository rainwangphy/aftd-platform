import AFTD.Prelude
import AFTD.Kb.Physics.PolynomialPhysHermite
import AFTD.Kb.Physics.PolynomialPhysHermiteOne
import AFTD.Kb.Physics.PolynomialPhysHermiteSucc
import AFTD.Kb.Physics.PolynomialPhysHermiteZero
import AFTD.Kb.Tcs.CslibOmegaSequenceTakeSucc'

/-!
# Polynomial.derivative_physHermite_succ

Topic: classical_mechanics   Node: 6064cca1a4e3

Provenance: formalization of a published result. Source: Physlib, `Polynomial.derivative_physHermite_succ`. Lean proof by Gregory J. Loges, Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/SpecialFunctions/PhysHermite.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Polynomial.derivative_physHermite_succ
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Nat in
lemma Polynomial.derivative_physHermite_succ : (n : ℕ) →
    derivative (physHermite (n + 1)) = 2 * (n + 1) • physHermite n
  | 0 => by simp [physHermite_one]
  | n + 1 => by
    rw [physHermite_succ]
    simp only [derivative_physHermite_succ n, nsmul_eq_mul, Nat.cast_ofNat, Nat.cast_add,
      Nat.cast_one, derivative_sub, derivative_mul, derivative_ofNat, zero_mul, derivative_X,
      mul_one, zero_add, derivative_add, derivative_natCast, derivative_one, add_zero]
    simp only [physHermite_succ, nsmul_eq_mul]
    ring

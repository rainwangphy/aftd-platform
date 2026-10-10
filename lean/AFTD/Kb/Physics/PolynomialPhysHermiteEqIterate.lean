import AFTD.Prelude
import AFTD.Kb.Physics.PolynomialPhysHermite
import AFTD.Kb.Physics.PolynomialPhysHermiteSucc

/-!
# Polynomial.physHermite_eq_iterate

Topic: classical_mechanics   Node: 53bf7f38a7a2

Provenance: formalization of a published result. Source: Physlib, `Polynomial.physHermite_eq_iterate`. Lean proof by Gregory J. Loges, Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/SpecialFunctions/PhysHermite.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Rodrigues formula `physHermite n = (2x - d/dx)ⁿ 1`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Nat in
/-- The Rodrigues formula `physHermite n = (2x - d/dx)ⁿ 1`. -/
lemma Polynomial.physHermite_eq_iterate (n : ℕ) :
    physHermite n = (fun p => 2 * X * p - derivative p)^[n] 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Function.iterate_succ_apply', ← ih, physHermite_succ]

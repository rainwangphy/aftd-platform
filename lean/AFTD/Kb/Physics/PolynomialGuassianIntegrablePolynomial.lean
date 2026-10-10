import AFTD.Prelude
import AFTD.Kb.Physics.PolynomialGuassianIntegrablePolynomialCons

/-!
# Polynomial.guassian_integrable_polynomial

Topic: classical_mechanics   Node: d4be958162fd

Provenance: formalization of a published result. Source: Physlib, `Polynomial.guassian_integrable_polynomial`. Lean proof by Gregory J. Loges, Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/SpecialFunctions/PhysHermite.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Polynomial.guassian_integrable_polynomial
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Nat in
@[fun_prop]
lemma Polynomial.guassian_integrable_polynomial {b : ℝ} (hb : 0 < b) (P : Polynomial ℤ) :
    MeasureTheory.Integrable fun x : ℝ => (P.aeval x) * Real.exp (-b * x ^ 2) := by
  simpa using guassian_integrable_polynomial_cons (c := 1) hb P

import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.DaRun

/-!
# Polynomial.physHermite

Topic: classical_mechanics   Node: f230ec3de68b

Provenance: formalization of a published result. Source: Physlib, `Polynomial.physHermite`. Lean proof by Gregory J. Loges, Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/SpecialFunctions/PhysHermite.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The physicist's Hermite polynomials are defined as polynomials over `ℤ` in `X` recursively with `physHermite 0 = 1` and `physHermite (n + 1) = 2 • X * physHermite n - derivative (physHermite n)`. This polynomial will often be cast as a function `ℝ → ℝ` by evaluating the polynomial at `X`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Nat in
/-- The physicist's Hermite polynomials are defined as polynomials over `ℤ` in `X` recursively with `physHermite 0 = 1` and `physHermite (n + 1) = 2 • X * physHermite n - derivative (physHermite n)`. This polynomial will often be cast as a function `ℝ → ℝ` by evaluating the polynomial at `X`. -/
noncomputable def Polynomial.physHermite : ℕ → Polynomial ℤ
  | 0 => 1
  | n + 1 => 2 • X * physHermite n - derivative (physHermite n)

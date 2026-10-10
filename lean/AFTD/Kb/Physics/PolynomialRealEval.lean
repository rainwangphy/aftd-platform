import AFTD.Prelude

/-!
# Polynomial.realEval

Topic: classical_mechanics   Node: e3618a566485

Provenance: formalization of a published result. Source: Physlib, `Polynomial.realEval`. Lean proof by Gregory J. Loges, Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/SpecialFunctions/PhysHermite.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cast an integer polynomial to a function `ℝ → ℝ` by evaluation of the indeterminant.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Nat in
/-- Cast an integer polynomial to a function `ℝ → ℝ` by evaluation of the indeterminant. -/
@[coe]
noncomputable abbrev Polynomial.realEval (p : Polynomial ℤ) : ℝ → ℝ := fun x ↦ p.aeval x

import AFTD.Prelude

/-!
# Space.oddNormIteratedLaplacianCoeff_factor_ne_zero

Topic: classical_mechanics   Node: 0805a1ff2917

Provenance: formalization of a published result. Source: Physlib, `Space.oddNormIteratedLaplacianCoeff_factor_ne_zero`. Lean proof by Lazar Milikic, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/SpaceAndTime/Space/Norm/IteratedLaplacian.lean (Copyright (c) 2026 Lazar Milikic. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Space.oddNormIteratedLaplacianCoeff_factor_ne_zero
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SchwartzMap NNReal in
open MeasureTheory in
open Distribution in
lemma Space.oddNormIteratedLaplacianCoeff_factor_ne_zero {m k : ℕ} (hk : k < m) :
    ((((1 : ℤ) - 2 * (k : ℤ) : ℤ) : ℝ) *
      ((((1 : ℤ) - 2 * (k : ℤ) - 2 + (2 * m + 1 : ℤ) : ℤ) : ℝ))) ≠ 0 := by
  apply mul_ne_zero
  · have h : (1 : ℤ) - 2 * (k : ℤ) ≠ 0 := by omega
    exact_mod_cast h
  · have h : (1 : ℤ) - 2 * (k : ℤ) - 2 + (2 * m + 1 : ℤ) ≠ 0 := by omega
    exact_mod_cast h

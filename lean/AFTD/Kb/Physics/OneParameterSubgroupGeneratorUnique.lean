import AFTD.Prelude

/-!
# OneParameterSubgroup.generator_unique

Topic: classical_mechanics   Node: 7f6d33c4a173

Provenance: formalization of a published result. Source: Physlib, `OneParameterSubgroup.generator_unique`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/OneParameterSubgroups/Basic.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Any exponential generator of a one-parameter subgroup is its derivative at zero.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Filter Topology in
variable {E : Type*} [NormedRing E] [NormedAlgebra ℝ E] [CompleteSpace E] in
/-- Any exponential generator of a one-parameter subgroup is its derivative at zero. -/
lemma OneParameterSubgroup.generator_unique (U : AddChar ℝ E) (A : E)
    (h : ∀ t : ℝ, U t = NormedSpace.exp (t • A)) : A = deriv U 0 := by
  simp [funext h, (hasDerivAt_exp_smul_const A (0 : ℝ)).deriv]

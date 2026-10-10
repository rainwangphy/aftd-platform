import AFTD.Prelude

/-!
# Matrix.tsum_eq_zero

Topic: classical_mechanics   Node: 1dd87f6a02f6

Provenance: formalization of a published result. Source: Physlib, `Matrix.tsum_eq_zero`. Lean proof by Matteo Cipollina, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/DataStructures/Matrix/LieTrace.lean (Copyright (c) 2025 Matteo Cipollina. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If every term of a series is zero, then its sum is zero.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators Topology in
variable {𝕂 m n : Type*} in
/-- If every term of a series is zero, then its sum is zero. -/
lemma Matrix.tsum_eq_zero
    {β : Type*} [TopologicalSpace β] [AddCommMonoid β]
    {f : ℕ → β} (h : ∀ n, f n = 0) :
    (∑' n, f n) = 0 := by
  simp_all only [tsum_zero]

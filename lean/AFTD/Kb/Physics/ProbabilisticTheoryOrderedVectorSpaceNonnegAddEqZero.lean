import AFTD.Prelude
import AFTD.Kb.Physics.ProbabilisticTheoryOrderedVectorSpace

/-!
# ProbabilisticTheory.OrderedVectorSpace.nonneg_add_eq_zero

Topic: quantum_mechanics   Node: e93dc54acd2b

Provenance: formalization of a published result. Source: Physlib, `ProbabilisticTheory.OrderedVectorSpace.nonneg_add_eq_zero`. Lean proof by Tom Ole Diem, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/ProbabilisticTheory/OrderUnit/Basic.lean (Copyright (c) 2026 Tom Ole Diem. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A nonnegative vector that adds with another nonnegative vector to `0` is itself `0`: the positive cone meets its negation only at `0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ProbabilisticTheory in
variable {E : Type*} [OrderedVectorSpace E] in
/-- A nonnegative vector that adds with another nonnegative vector to `0` is itself `0`: the positive cone meets its negation only at `0`. -/
lemma ProbabilisticTheory.OrderedVectorSpace.nonneg_add_eq_zero {A B : E} (hA : 0 ≤ A) (hB : 0 ≤ B) (hAB : A + B = 0) : A = 0 :=
  le_antisymm (hAB ▸ le_add_of_nonneg_right hB) hA

import AFTD.Prelude

/-!
# Cslib.MachineLearning.PACLearning.hypothesisError

Topic: learning   Node: 9f7af0069969

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.hypothesisError`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The *symmetric-difference error* of a hypothesis `h` with respect to a target concept `c` (both viewed as subsets of `α`) under distribution `P`, defined as `P(h ∆ c)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
variable {α : Type*} [MeasurableSpace α] in
/-- The *symmetric-difference error* of a hypothesis `h` with respect to a target concept `c` (both viewed as subsets of `α`) under distribution `P`, defined as `P(h ∆ c)`. -/
noncomputable def Cslib.MachineLearning.PACLearning.hypothesisError (P : Measure α) (h c : Set α) : ℝ≥0∞ :=
  P (symmDiff h c)

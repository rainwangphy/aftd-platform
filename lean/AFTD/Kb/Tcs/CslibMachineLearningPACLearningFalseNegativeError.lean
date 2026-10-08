import AFTD.Prelude

/-!
# Cslib.MachineLearning.PACLearning.falseNegativeError

Topic: learning   Node: 8ee016a14918

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.falseNegativeError`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The *false negative error* `P(c \ h)` — points in the concept but classified negative.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
variable {α : Type*} [MeasurableSpace α] in
/-- The *false negative error* `P(c \ h)` — points in the concept but classified negative. -/
noncomputable def Cslib.MachineLearning.PACLearning.falseNegativeError (P : Measure α) (h c : Set α) : ℝ≥0∞ :=
  P (c \ h)

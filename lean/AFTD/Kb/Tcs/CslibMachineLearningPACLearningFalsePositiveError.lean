import AFTD.Prelude

/-!
# Cslib.MachineLearning.PACLearning.falsePositiveError

Topic: learning   Node: 5c5014792f93

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.falsePositiveError`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The *false positive error* `P(h \ c)` — points classified positive but not in the concept.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
variable {α : Type*} [MeasurableSpace α] in
/-- The *false positive error* `P(h \ c)` — points classified positive but not in the concept. -/
noncomputable def Cslib.MachineLearning.PACLearning.falsePositiveError (P : Measure α) (h c : Set α) : ℝ≥0∞ :=
  P (h \ c)

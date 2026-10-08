import AFTD.Prelude

/-!
# Cslib.MachineLearning.PACLearning.error

Topic: learning   Node: 150ae041fab9

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.error`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The *prediction error* (0-1 loss) of a hypothesis `h` under a joint distribution `D` on `α × β`, defined as the probability that the prediction disagrees with the label: `D({(x, y) | h(x) ≠ y})`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
variable {α : Type*} {β : Type*} [MeasurableSpace α] [MeasurableSpace β] in
/-- The *prediction error* (0-1 loss) of a hypothesis `h` under a joint distribution `D` on `α × β`, defined as the probability that the prediction disagrees with the label: `D({(x, y) | h(x) ≠ y})`. -/
noncomputable def Cslib.MachineLearning.PACLearning.error (D : Measure (α × β)) (h : α → β) : ℝ≥0∞ :=
  D {p : α × β | h p.1 ≠ p.2}

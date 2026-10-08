import AFTD.Prelude
import AFTD.Kb.Tcs.CslibMachineLearningPACLearningLabeledSample

/-!
# Cslib.MachineLearning.PACLearning.Learner

Topic: learning   Node: e2bfd8a53717

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.Learner`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A *learner* using `m` samples is a function that takes a labeled sample and produces a hypothesis (a function from the domain to the label type).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
/-- A *learner* using `m` samples is a function that takes a labeled sample and produces a hypothesis (a function from the domain to the label type). -/
abbrev Cslib.MachineLearning.PACLearning.Learner (α β : Type*) (m : ℕ) := LabeledSample α β m → (α → β)

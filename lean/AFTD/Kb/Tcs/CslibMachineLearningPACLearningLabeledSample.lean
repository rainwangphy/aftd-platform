import AFTD.Prelude

/-!
# Cslib.MachineLearning.PACLearning.LabeledSample

Topic: learning   Node: 17bb261a9ecc

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.LabeledSample`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A *labeled sample* of size `m` over domain `α` with label type `β` is a finite sequence of `(point, label)` pairs.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
/-- A *labeled sample* of size `m` over domain `α` with label type `β` is a finite sequence of `(point, label)` pairs. -/
abbrev Cslib.MachineLearning.PACLearning.LabeledSample (α β : Type*) (m : ℕ) := Fin m → (α × β)

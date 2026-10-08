import AFTD.Prelude

/-!
# Cslib.MachineLearning.PACLearning.ConceptClass

Topic: learning   Node: 3a9f2084dc57

Provenance: formalization of a published result. Source: CSLib, `Cslib.MachineLearning.PACLearning.ConceptClass`. Lean proof by Samuel Schlesinger, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/MachineLearning/PACLearning/Defs.lean (Copyright (c) 2026 Samuel Schlesinger. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A *concept class* over domain `α` with label type `β` is a set of functions `α → β`. For binary classification (`β = Bool`), this is equivalent to a collection of subsets of `α` via the characteristic function.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory Set in
open scoped ENNReal NNReal in
/-- A *concept class* over domain `α` with label type `β` is a set of functions `α → β`. For binary classification (`β = Bool`), this is equivalent to a collection of subsets of `α` via the characteristic function. -/
abbrev Cslib.MachineLearning.PACLearning.ConceptClass (α β : Type*) := Set (α → β)

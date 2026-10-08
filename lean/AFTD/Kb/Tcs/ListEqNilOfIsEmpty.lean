import AFTD.Prelude

/-!
# List.eq_nil_ofIsEmpty

Topic: automata   Node: 7a57b03f5ba1

Provenance: formalization of a published result. Source: CSLib, `List.eq_nil_ofIsEmpty`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Languages/Language.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`[]` is the only list over an empty type.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α : Type*} in
/-- `[]` is the only list over an empty type. -/
theorem List.eq_nil_ofIsEmpty [IsEmpty α] (xl : List α) : xl = [] := by
  have hu := List.uniqueOfIsEmpty (α := α)
  simp [Unique.eq_default]

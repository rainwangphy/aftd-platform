import AFTD.Prelude

/-!
# Language.mem_sub_one

Topic: automata   Node: af1b5f54527c

Provenance: formalization of a published result. Source: CSLib, `Language.mem_sub_one`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Languages/Language.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Language.mem_sub_one
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set List in
open scoped Computability in
variable {α : Type*} {l m : Language α} in
@[simp, scoped grind =]
theorem Language.mem_sub_one (x : List α) : x ∈ (l - 1) ↔ x ∈ l ∧ x ≠ [] :=
  Iff.rfl

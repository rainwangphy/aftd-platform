import AFTD.Prelude

/-!
# Language.reverse_sub

Topic: automata   Node: 8287dd5da0fb

Provenance: formalization of a published result. Source: CSLib, `Language.reverse_sub`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Languages/Language.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Language.reverse_sub
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set List in
open scoped Computability in
variable {α : Type*} {l m : Language α} in
@[simp, scoped grind =]
theorem Language.reverse_sub (l m : Language α) : (l - m).reverse = l.reverse - m.reverse := by
  ext x; simp [mem_sub]

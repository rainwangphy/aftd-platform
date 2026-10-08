import AFTD.Prelude
import AFTD.Kb.Tcs.LanguageReverseSub
import AFTD.Kb.Tcs.LanguageSubOneMul

/-!
# Language.mul_sub_one

Topic: automata   Node: 8d5774de6c32

Provenance: formalization of a published result. Source: CSLib, `Language.mul_sub_one`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Languages/Language.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Language.mul_sub_one
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set List in
open scoped Computability in
variable {α : Type*} {l m : Language α} in
@[scoped grind =]
theorem Language.mul_sub_one : l * (l - 1) = l * l - 1 := by
  calc
    _ = (l * (l - 1)).reverse.reverse := by rw [reverse_reverse]
    _ = ((l.reverse - 1) * l.reverse).reverse := by rw [reverse_mul, reverse_sub, reverse_one]
    _ = (l.reverse * l.reverse - 1).reverse := by rw [sub_one_mul]
    _ = _ := by rw [reverse_sub, reverse_one, reverse_mul, reverse_reverse]

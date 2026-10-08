import AFTD.Prelude
import AFTD.Kb.Tcs.ListEqNilOfIsEmpty

/-!
# Language.eq_zero_or_one_ofIsEmpty

Topic: automata   Node: eed12b93dbb1

Provenance: formalization of a published result. Source: CSLib, `Language.eq_zero_or_one_ofIsEmpty`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Languages/Language.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`0` and `1` are the only possible languages over an empty type.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set List in
open scoped Computability in
variable {α : Type*} {l m : Language α} in
/-- `0` and `1` are the only possible languages over an empty type. -/
theorem Language.eq_zero_or_one_ofIsEmpty [IsEmpty α] (l : Language α) : l = 0 ∨ l = 1 := by
  by_cases h : l = 0
  · simp [h]
  · right
    ext xl
    obtain ⟨yl, _⟩ := nonempty_iff_ne_empty.mpr h
    obtain ⟨rfl⟩ := eq_nil_ofIsEmpty xl
    obtain ⟨rfl⟩ := eq_nil_ofIsEmpty yl
    simpa

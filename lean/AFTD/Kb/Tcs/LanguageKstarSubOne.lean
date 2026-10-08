import AFTD.Prelude

/-!
# Language.kstar_sub_one

Topic: automata   Node: 1cd657cef72b

Provenance: formalization of a published result. Source: CSLib, `Language.kstar_sub_one`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Languages/Language.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A grind regression found moving to nightly-2026-03-31 (changes from lean#13166)
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set List in
open scoped Computability in
variable {α : Type*} {l m : Language α} in
/-- A grind regression found moving to nightly-2026-03-31 (changes from lean#13166) -/
@[scoped grind =]
theorem Language.kstar_sub_one : l∗ - 1 = (l - 1) * l∗ := by
  ext x; constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨xl, rfl, h_xl⟩ := kstar_def_nonempty l ▸ h1
    have h3 : ¬ xl = [] := by grind [one_def]
    obtain ⟨x, xl', h_xl'⟩ := exists_cons_of_ne_nil h3
    subst h_xl'
    refine ⟨x, mem_preimage.mp (h_xl x ?_), xl'.flatten, join_mem_kstar ?_, ?_⟩ <;> grind
  · rintro ⟨y, ⟨h_y, h_1⟩, z, h_z, rfl⟩
    refine ⟨?_, ?_⟩
    · apply (show l * l∗ ≤ l∗ by exact mul_kstar_le_kstar)
      exact ⟨y, h_y, z, h_z, rfl⟩
    · grind [one_def, append_eq_nil_iff]

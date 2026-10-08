import AFTD.Prelude
import AFTD.Kb.Tcs.LanguageMemSubOne

/-!
# Language.sub_one_mul

Topic: automata   Node: dffc48ed56bb

Provenance: formalization of a published result. Source: CSLib, `Language.sub_one_mul`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Languages/Language.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A grind regression found moving to nightly-2026-03-31 (changes from lean#13166)
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set List in
open scoped Computability in
variable {α : Type*} {l m : Language α} in
/-- A grind regression found moving to nightly-2026-03-31 (changes from lean#13166) -/
@[scoped grind =]
theorem Language.sub_one_mul : (l - 1) * l = l * l - 1 := by
  ext x; constructor
  · rintro ⟨u, h_u, v, h_v, rfl⟩
    constructor
    · exact ⟨u, Set.mem_of_mem_inter_left h_u, v, h_v, rfl⟩
    · by_contra h
      have := mem_sub_one u |>.mp h_u
      have := mem_one (u ++ v) |>.mp h
      grind [append_eq_nil_iff]
  · rintro ⟨⟨u, h_u, v, h_v, rfl⟩, h_x⟩
    rcases eq_or_ne u [] with (rfl | h_u')
    · use v, (mem_sub l 1 v |>.mpr) ⟨h_v, Not.intro h_x⟩, []
      grind [mem_sub, mem_one]
    · use u, (mem_sub_one u).mpr ⟨h_u, h_u'⟩, v

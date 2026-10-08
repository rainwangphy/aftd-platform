import AFTD.Prelude

/-!
# Language.mem_biSup

Topic: automata   Node: 7d104aca7d7c

Provenance: formalization of a published result. Source: CSLib, `Language.mem_biSup`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Languages/Language.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A grind regression found moving to nightly-2026-03-31 (changes from lean#13166)
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set List in
open scoped Computability in
variable {α : Type*} {l m : Language α} in
/-- A grind regression found moving to nightly-2026-03-31 (changes from lean#13166) -/
@[simp]
theorem Language.mem_biSup {I : Type*} (s : Set I) (l : I → Language α) (x : List α) :
    (x ∈ ⨆ i ∈ s, l i) ↔ ∃ i ∈ s, x ∈ l i where
  mp h := bex_def.mp (mem_iUnion₂.mp h)
  mpr h :=  mem_iUnion₂.mpr (bex_def.mpr h)

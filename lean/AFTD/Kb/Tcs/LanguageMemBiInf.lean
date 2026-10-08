import AFTD.Prelude

/-!
# Language.mem_biInf

Topic: automata   Node: a34a7558cd9e

Provenance: formalization of a published result. Source: CSLib, `Language.mem_biInf`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Languages/Language.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Language.mem_biInf
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set List in
open scoped Computability in
variable {α : Type*} {l m : Language α} in
@[simp]
theorem Language.mem_biInf {I : Type*} (s : Set I) (l : I → Language α) (x : List α) :
    (x ∈ ⨅ i ∈ s, l i) ↔ ∀ i ∈ s, x ∈ l i :=
  mem_iInter₂

import AFTD.Prelude

/-!
# Language.le_one_iff_eq

Topic: automata   Node: f1d703d5bd8b

Provenance: formalization of a published result. Source: CSLib, `Language.le_one_iff_eq`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Languages/Language.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Language.le_one_iff_eq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Set List in
open scoped Computability in
variable {α : Type*} {l m : Language α} in
theorem Language.le_one_iff_eq : l ≤ 1 ↔ l = 0 ∨ l = 1 :=
  subset_singleton_iff_eq

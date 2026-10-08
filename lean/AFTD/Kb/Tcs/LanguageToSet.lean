import AFTD.Prelude

/-!
# Language.toSet

Topic: automata   Node: 48425ee3b6d1

Provenance: formalization of a published result. Source: CSLib, `Language.toSet`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/Languages/OmegaLanguage.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The set of lists in a language.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α β γ : Type*} in
/-- The set of lists in a language. -/
def Language.toSet (l : Language α) : Set (List α) := l

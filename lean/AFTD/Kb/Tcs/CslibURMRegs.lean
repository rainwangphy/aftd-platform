import AFTD.Prelude

/-!
# Cslib.URM.Regs

Topic: computability   Node: 65683b880132

Provenance: formalization of a published result. Source: CSLib, `Cslib.URM.Regs`. Lean proof by Jesse Alama, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Computability/URM/Defs.lean (Copyright (c) 2026 Jesse Alama. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Register contents: maps register indices to natural number contents. Uses the functional representation `ℕ → ℕ` for efficiency with rewrites, following the advice from the `grind` tactic documentation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Register contents: maps register indices to natural number contents. Uses the functional representation `ℕ → ℕ` for efficiency with rewrites, following the advice from the `grind` tactic documentation. -/
abbrev Cslib.URM.Regs := ℕ → ℕ

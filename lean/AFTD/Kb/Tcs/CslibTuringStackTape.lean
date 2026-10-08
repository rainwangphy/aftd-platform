import AFTD.Prelude

/-!
# Cslib.Turing.StackTape

Topic: algorithms   Node: 3fa08ad128b0

Provenance: formalization of a published result. Source: CSLib, `Cslib.Turing.StackTape`. Lean proof by Bolton Bailey, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/StackTape.lean (Copyright (c) 2026 Bolton Bailey. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An infinite tape representation using a list of `Option` values, where the list is eventually `none`. Represented as a `List (Option Symbol)` that does not end with `none`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- An infinite tape representation using a list of `Option` values, where the list is eventually `none`. Represented as a `List (Option Symbol)` that does not end with `none`. -/
structure Cslib.Turing.StackTape (Symbol : Type*) where
  /-- The underlying list representation -/
  toList : List (Option Symbol)
  /--
  The list can be empty (i.e. `none`),
  but if it is not empty, the last element is not (`some`) `none`
  -/
  toList_getLast?_ne_some_none : toList.getLast? ≠ some none

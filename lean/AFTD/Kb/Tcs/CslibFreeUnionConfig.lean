import AFTD.Prelude

/-!
# Cslib.FreeUnionConfig

Topic: algorithms   Node: 5980f8bfe4a7

Provenance: formalization of a published result. Source: CSLib, `Cslib.FreeUnionConfig`. Lean proof by Fabrizio Montesi, Kenny Lau, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/HasFresh.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Configuration for the `free_union` term elaborator.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Lean Elab Term Meta Parser Tactic in
/-- Configuration for the `free_union` term elaborator. -/
structure Cslib.FreeUnionConfig where
  /-- For `free_union Var`, include all `x : Var`. Defaults to true. -/
  singleton : Bool := true
  /-- For `free_union Var`, include all `xs : Finset Var`. Defaults to true. -/
  finset : Bool := true

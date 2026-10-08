import AFTD.Prelude

/-!
# Cslib.FreeM.ContF

Topic: computability   Node: 3fa64b6ea352

Provenance: formalization of a published result. Source: CSLib, `Cslib.FreeM.ContF`. Lean proof by Tanner Duve, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Control/Monad/Free/Effects.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Type constructor for continuation operations.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w w' w'' in
/-- Type constructor for continuation operations. -/
inductive Cslib.FreeM.ContF (r : Type u) (α : Type v) where
  /-- Call with current continuation: provides access to the current continuation. -/
  | callCC : ((α → r) → r) → ContF r α

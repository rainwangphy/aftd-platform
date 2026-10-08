import AFTD.Prelude

/-!
# Cslib.FreeM.ReaderF

Topic: computability   Node: aad5f7509c60

Provenance: formalization of a published result. Source: CSLib, `Cslib.FreeM.ReaderF`. Lean proof by Tanner Duve, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Control/Monad/Free/Effects.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Type constructor for reader operations.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w w' w'' in
/-- Type constructor for reader operations. -/
inductive Cslib.FreeM.ReaderF (σ : Type u) : Type u → Type u where
  | read : ReaderF σ σ

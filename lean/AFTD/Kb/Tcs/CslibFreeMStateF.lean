import AFTD.Prelude

/-!
# Cslib.FreeM.StateF

Topic: computability   Node: 847f067211fd

Provenance: formalization of a published result. Source: CSLib, `Cslib.FreeM.StateF`. Lean proof by Tanner Duve, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Control/Monad/Free/Effects.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Type constructor for state operations.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w w' w'' in
/-- Type constructor for state operations. -/
inductive Cslib.FreeM.StateF (σ : Type u) : Type u → Type u where
  /-- Get the current state. -/
  | get : StateF σ σ
  /-- Set the state. -/
  | set : σ → StateF σ PUnit

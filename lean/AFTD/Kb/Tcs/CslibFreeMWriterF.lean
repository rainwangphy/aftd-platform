import AFTD.Prelude

/-!
# Cslib.FreeM.WriterF

Topic: computability   Node: 042b4ea2f573

Provenance: formalization of a published result. Source: CSLib, `Cslib.FreeM.WriterF`. Lean proof by Tanner Duve, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Control/Monad/Free/Effects.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Type constructor for writer operations. Writer has a single effect, so the definition has just one constructor.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w w' w'' in
/-- Type constructor for writer operations. Writer has a single effect, so the definition has just one constructor. -/
inductive Cslib.FreeM.WriterF (ω : Type u) : Type v → Type u
  /-- Write a value to the log. -/ | tell : ω → WriterF ω PUnit

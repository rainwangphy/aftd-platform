import AFTD.Prelude

/-!
# Cslib.Logic.InferenceSystem

Topic: proof_theory   Node: d063f087afbe

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.InferenceSystem`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Logic/InferenceSystem.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The notation typeclass for inference systems. This enables the notation `S⇓a`, where `S` is a tag for the inference system and `a : α` is a derivable value.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The notation typeclass for inference systems. This enables the notation `S⇓a`, where `S` is a tag for the inference system and `a : α` is a derivable value. -/
class Cslib.Logic.InferenceSystem (S : Type*) (α : Type*) where
  /--
  `S⇓a` is a derivation of `a`, that is, a witness that `a` is derivable in the system `S`.
  The meaning of this notation is type-dependent.
  -/
  derivation (a : α) : Sort v

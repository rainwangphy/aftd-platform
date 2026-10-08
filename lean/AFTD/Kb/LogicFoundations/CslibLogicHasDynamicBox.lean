import AFTD.Prelude

/-!
# Cslib.Logic.HasDynamicBox

Topic: proof_theory   Node: ffbb5e5504c2

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.HasDynamicBox`. Lean proof by Fabrizio Montesi, Thomas Waring, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Logic/Operators.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The type `α` has a dynamic box modality with action type `β` (`d[a]φ`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The type `α` has a dynamic box modality with action type `β` (`d[a]φ`). -/
class Cslib.Logic.HasDynamicBox (α β : Type*) where
  /-- `b` is necessarily valid after `a`. -/
  dynBox (a : β) (b : α) : α

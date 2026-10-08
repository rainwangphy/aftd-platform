import AFTD.Prelude

/-!
# Cslib.Logic.HasDynamicDiamond

Topic: proof_theory   Node: ca94eaafce69

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.HasDynamicDiamond`. Lean proof by Fabrizio Montesi, Thomas Waring, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Logic/Operators.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The type `α` has a dynamic diamond modality with action type `β` (`d⟨a⟩φ`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The type `α` has a dynamic diamond modality with action type `β` (`d⟨a⟩φ`). -/
class Cslib.Logic.HasDynamicDiamond (α β : Type*) where
  /-- `b` is possibly valid after `a`. -/
  dynDiamond (a : β) (b : α) : α

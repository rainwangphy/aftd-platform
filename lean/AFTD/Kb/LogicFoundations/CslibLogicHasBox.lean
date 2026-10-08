import AFTD.Prelude

/-!
# Cslib.Logic.HasBox

Topic: proof_theory   Node: e58269b2709b

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.HasBox`. Lean proof by Fabrizio Montesi, Thomas Waring, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Logic/Operators.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The type `α` has a box modality (`□`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The type `α` has a box modality (`□`). -/
class Cslib.Logic.HasBox (α : Type*) where
  /-- `a` is valid in all immediately reachable states. -/
  box (a : α) : α

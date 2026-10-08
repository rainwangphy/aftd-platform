import AFTD.Prelude
import AFTD.Kb.Tcs.CslibHasFresh

/-!
# Cslib.HasFresh.to_infinite

Topic: algorithms   Node: 7a5308809212

Provenance: formalization of a published result. Source: CSLib, `Cslib.HasFresh.to_infinite`. Lean proof by Fabrizio Montesi, Kenny Lau, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/HasFresh.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`HasFresh α` implies a computably infinite type.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
/-- `HasFresh α` implies a computably infinite type. -/
instance Cslib.HasFresh.to_infinite (α : Type u) [HasFresh α] : Infinite α := by
  apply Infinite.of_not_fintype
  rintro ⟨elems, _⟩
  grind [fresh_notMem elems]

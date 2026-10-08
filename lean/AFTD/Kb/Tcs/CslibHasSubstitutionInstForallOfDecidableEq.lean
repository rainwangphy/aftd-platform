import AFTD.Prelude
import AFTD.Kb.Tcs.CslibHasSubstitution

/-!
# Cslib.HasSubstitution.instForallOfDecidableEq

Topic: computability   Node: bf832f5c9a85

Provenance: formalization of a published result. Source: CSLib, `Cslib.HasSubstitution.instForallOfDecidableEq`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Syntax/HasSubstitution.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.HasSubstitution.instForallOfDecidableEq
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance Cslib.HasSubstitution.instForallOfDecidableEq [DecidableEq α] : HasSubstitution (α → β) α β where
  subst := Function.update

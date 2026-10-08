import AFTD.Prelude
import AFTD.Kb.Tcs.CslibHasContext
import AFTD.Kb.Tcs.CslibHasHContext

/-!
# Cslib.HasContext.Context

Topic: computability   Node: 24802f29543c

Provenance: formalization of a published result. Source: CSLib, `Cslib.HasContext.Context`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Syntax/Context.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.HasContext.Context
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[inherit_doc HasHContext.Context]
def Cslib.HasContext.Context (α : Type*) [HasContext α] : Type* := HasHContext.Context α α

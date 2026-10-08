import AFTD.Prelude
import AFTD.Kb.Tcs.CslibHasTau

/-!
# Cslib.DecidableEqTau

Topic: computability   Node: 8d2219f5c050

Provenance: formalization of a published result. Source: CSLib, `Cslib.DecidableEqTau`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/HasTau.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Checking whether an element is `τ` is decidable.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v in
/-- Checking whether an element is `τ` is decidable. -/
abbrev Cslib.DecidableEqTau (α : Type*) [HasTau α] := ∀ a : α, Decidable (a = HasTau.τ)

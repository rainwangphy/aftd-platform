import AFTD.Prelude

/-!
# Cslib.DecidableEqZero

Topic: algorithms   Node: 7c2712e1de33

Provenance: formalization of a published result. Source: CSLib, `Cslib.DecidableEqZero`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/DecidableEqZero.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Equality to `Zero` is decidable for all elements of a type (`α`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Equality to `Zero` is decidable for all elements of a type (`α`). -/
abbrev Cslib.DecidableEqZero (α : Type*) [Zero α] := ∀ a : α, Decidable (a = 0)

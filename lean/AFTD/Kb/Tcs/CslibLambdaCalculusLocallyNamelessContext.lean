import AFTD.Prelude

/-!
# Cslib.LambdaCalculus.LocallyNameless.Context

Topic: computability   Node: f005a0e6f901

Provenance: formalization of a published result. Source: CSLib, `Cslib.LambdaCalculus.LocallyNameless.Context`. Lean proof by Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/LambdaCalculus/LocallyNameless/Context.lean (Copyright (c) 2025 Chris Henson. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A typing context is a list of free variables and corresponding types.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v in
variable {α : Type u} {β : Type v} in
variable [DecidableEq α] in
/-- A typing context is a list of free variables and corresponding types. -/
abbrev Cslib.LambdaCalculus.LocallyNameless.Context (α : Type u) (β : Type v) := List ((_ : α) × β)

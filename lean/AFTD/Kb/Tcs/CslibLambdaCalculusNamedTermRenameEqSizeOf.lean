import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLambdaCalculusNamedTerm
import AFTD.Kb.Tcs.CslibLambdaCalculusNamedTermRename

/-!
# Cslib.LambdaCalculus.Named.Term.rename.eq_sizeOf

Topic: computability   Node: e175b70b5cd2

Provenance: formalization of a published result. Source: CSLib, `Cslib.LambdaCalculus.Named.Term.rename.eq_sizeOf`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/LambdaCalculus/Named/Untyped/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Renaming preserves size.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {Var : Type u} in
/-- Renaming preserves size. -/
@[simp]
theorem Cslib.LambdaCalculus.Named.Term.rename.eq_sizeOf {m : Term Var} {x y : Var} [DecidableEq Var] :
  sizeOf (m.rename x y) = sizeOf m := by
  induction m <;> aesop (add simp [Term.rename])

import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLambdaCalculusNamedTerm
import AFTD.Kb.Tcs.CslibLambdaCalculusNamedTermFv
import AFTD.Kb.Tcs.CslibLambdaCalculusNamedTermBv

/-!
# Cslib.LambdaCalculus.Named.Term.vars

Topic: computability   Node: 81758ce9a3bb

Provenance: formalization of a published result. Source: CSLib, `Cslib.LambdaCalculus.Named.Term.vars`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/LambdaCalculus/Named/Untyped/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Variable names (free and bound) in a term.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {Var : Type u} in
/-- Variable names (free and bound) in a term. -/
def Cslib.LambdaCalculus.Named.Term.vars [DecidableEq Var] (m : Term Var) : Finset Var :=
  m.fv ∪ m.bv

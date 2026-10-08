import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLambdaCalculusNamedTerm

/-!
# Cslib.LambdaCalculus.Named.Term.fv

Topic: computability   Node: d85b45e607b5

Provenance: formalization of a published result. Source: CSLib, `Cslib.LambdaCalculus.Named.Term.fv`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/LambdaCalculus/Named/Untyped/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Free variables.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {Var : Type u} in
/-- Free variables. -/
def Cslib.LambdaCalculus.Named.Term.fv [DecidableEq Var] : Term Var → Finset Var
  | var x => {x}
  | abs x m => m.fv.erase x
  | app m n => m.fv ∪ n.fv

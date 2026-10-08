import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLambdaCalculusNamedTerm

/-!
# Cslib.LambdaCalculus.Named.Term.bv

Topic: computability   Node: 1e3a53108d00

Provenance: formalization of a published result. Source: CSLib, `Cslib.LambdaCalculus.Named.Term.bv`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/LambdaCalculus/Named/Untyped/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Bound variables.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {Var : Type u} in
/-- Bound variables. -/
def Cslib.LambdaCalculus.Named.Term.bv [DecidableEq Var] : Term Var → Finset Var
  | var _ => ∅
  | abs x m => m.bv ∪ {x} -- Could also be `insert x m.bv`
  | app m n => m.bv ∪ n.bv

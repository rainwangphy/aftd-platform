import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLambdaCalculusNamedTerm

/-!
# Cslib.LambdaCalculus.Named.Term.rename

Topic: computability   Node: f557139295c4

Provenance: formalization of a published result. Source: CSLib, `Cslib.LambdaCalculus.Named.Term.rename`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/LambdaCalculus/Named/Untyped/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Renaming, or variable substitution. `m.rename x y` renames `x` into `y` in `m`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {Var : Type u} in
/-- Renaming, or variable substitution. `m.rename x y` renames `x` into `y` in `m`. -/
def Cslib.LambdaCalculus.Named.Term.rename [DecidableEq Var] (m : Term Var) (x y : Var) : Term Var :=
  match m with
  | var z => if z = x then (var y) else (var z)
  | abs z m' =>
    if z = x then
      -- Shadowing
      abs z m'
    else
      abs z (m'.rename x y)
  | app n1 n2 => app (n1.rename x y) (n2.rename x y)

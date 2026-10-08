import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLambdaCalculusNamedTerm
import AFTD.Kb.Tcs.CslibLambdaCalculusNamedTermFv

/-!
# Cslib.LambdaCalculus.Named.Term.Subst

Topic: computability   Node: c6d10b8fe27f

Provenance: formalization of a published result. Source: CSLib, `Cslib.LambdaCalculus.Named.Term.Subst`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/LambdaCalculus/Named/Untyped/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Capture-avoiding substitution, as an inference system.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {Var : Type u} in
/-- Capture-avoiding substitution, as an inference system. -/
inductive Cslib.LambdaCalculus.Named.Term.Subst [DecidableEq Var] : Term Var → Var → Term Var → Term Var → Prop where
  | varHit : (var x).Subst x r r
  | varMiss : x ≠ y → (var y).Subst x r (var y)
  | absShadow : (abs x m).Subst x r (abs x m)
  | absIn : x ≠ y → y ∉ r.fv → m.Subst x r m' → (abs y m).Subst x r (abs y m')
  | app : m.Subst x r m' → n.Subst x r n' → (app m n).Subst x r (app m' n')

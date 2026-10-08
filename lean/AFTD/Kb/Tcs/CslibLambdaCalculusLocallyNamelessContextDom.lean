import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLambdaCalculusLocallyNamelessContext

/-!
# Cslib.LambdaCalculus.LocallyNameless.Context.dom

Topic: computability   Node: a7639b5186cf

Provenance: formalization of a published result. Source: CSLib, `Cslib.LambdaCalculus.LocallyNameless.Context.dom`. Lean proof by Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/LambdaCalculus/LocallyNameless/Context.lean (Copyright (c) 2025 Chris Henson. All rights reserved, Apache-2.0); 1 adapted; compiled here.

The domain of a context is the finite set of free variables it uses.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LambdaCalculus Cslib.LambdaCalculus.LocallyNameless in
universe u v in
variable {α : Type u} {β : Type v} in
variable [DecidableEq α] in
open List in
attribute [local grind =] Option.mem_def in
attribute [local grind _=_] List.append_eq in
attribute [local grind =] List.Nodup in
attribute [local grind _=_] List.singleton_append in
attribute [local grind =] Option.or_eq_some_iff in
attribute [local grind =] Option.or_eq_none_iff in
attribute [local grind _=_] List.mem_toFinset in
attribute [local grind =] List.nodupKeys_middle in
attribute [local grind →] List.perm_nodupKeys in
/-- The domain of a context is the finite set of free variables it uses. -/
@[simp, grind =]
def Cslib.LambdaCalculus.LocallyNameless.Context.dom (Γ : Context α β) : Finset α := Γ.keys.toFinset

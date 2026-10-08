import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLambdaCalculusLocallyNamelessContext
import AFTD.Kb.Tcs.CslibLambdaCalculusLocallyNamelessContextMapVal
import AFTD.Kb.Tcs.CslibLambdaCalculusLocallyNamelessContextDom
import AFTD.Kb.Tcs.CslibLambdaCalculusLocallyNamelessContextInstHasWellFormed

/-!
# Cslib.LambdaCalculus.LocallyNameless.Context.mapVal_keys

Topic: computability   Node: 17585f15bb9f

Provenance: formalization of a published result. Source: CSLib, `Cslib.LambdaCalculus.LocallyNameless.Context.mapVal_keys`. Lean proof by Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/LambdaCalculus/LocallyNameless/Context.lean (Copyright (c) 2025 Chris Henson. All rights reserved, Apache-2.0); 1 adapted; compiled here.

A mapping of values preserves keys.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LambdaCalculus Cslib.LambdaCalculus.LocallyNameless Cslib.LambdaCalculus.LocallyNameless.Context in
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
variable {Γ Δ : Context α β} in
omit [DecidableEq α] in
/-- A mapping of values preserves keys. -/
@[grind .]
lemma Cslib.LambdaCalculus.LocallyNameless.Context.mapVal_keys (f) : Γ.keys = (Γ.mapVal f).keys := by
  induction Γ <;> grind

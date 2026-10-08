import AFTD.Prelude
import AFTD.Kb.Tcs.CslibHasWellFormed
import AFTD.Kb.Tcs.CslibLambdaCalculusLocallyNamelessContext
import AFTD.Kb.Tcs.CslibLambdaCalculusLocallyNamelessContextDom

/-!
# Cslib.LambdaCalculus.LocallyNameless.Context.instHasWellFormed

Topic: computability   Node: 004c386be334

Provenance: formalization of a published result. Source: CSLib, `Cslib.LambdaCalculus.LocallyNameless.Context.instHasWellFormed`. Lean proof by Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/LambdaCalculus/LocallyNameless/Context.lean (Copyright (c) 2025 Chris Henson. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Cslib.LambdaCalculus.LocallyNameless.Context.instHasWellFormed
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
instance Cslib.LambdaCalculus.LocallyNameless.Context.instHasWellFormed : HasWellFormed (Context α β) :=
  ⟨NodupKeys⟩

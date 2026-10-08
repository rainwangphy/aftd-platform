import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IndexedLOrder
import AFTD.Kb.Tcs.G

/-!
# instFunLikeIndexedLOrderLinearOrder

Topic: general_equilibrium   Node: 2f7e43616f43

Provenance: formalization of a published result. Source: EconCSLib, `instFunLikeIndexedLOrderLinearOrder`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Scarf.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

instFunLikeIndexedLOrderLinearOrder
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open Finset in
variable {T : Type*} [Inhabited T] in
variable {I : Type*} in
instance instFunLikeIndexedLOrderLinearOrder : FunLike (IndexedLOrder I T) I (LinearOrder T) where
  coe := fun a => a.IST
  coe_injective := fun f g h => by cases f; cases g; congr

import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IndexedLOrder
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsCell
import AFTD.Kb.GameTheoryEconomics.InstFunLikeIndexedLOrderLinearOrder

/-!
# IndexedLOrder.isTypedNC

Topic: general_equilibrium   Node: 7d2b6255951b

Provenance: formalization of a published result. Source: EconCSLib, `IndexedLOrder.isTypedNC`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Scarf.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`(σ, C)` is a **typed nearly-colorful** cell of type `i`: a dominant cell where `i` is the unique color in `C` missing from `σ.image c`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open IndexedLOrder in
open Classical in
variable {T : Type*} [Inhabited T] in
variable {I : Type*} in
variable [IST : IndexedLOrder I T] in
set_option quotPrecheck false in
variable (σ : Finset T) (C : Finset I) in
variable [DecidableEq T] [DecidableEq I] in
open Classical in
variable (c : T → I) (σ : Finset T) (C : Finset I) in
/-- `(σ, C)` is a **typed nearly-colorful** cell of type `i`: a dominant cell where `i` is the unique color in `C` missing from `σ.image c`. -/
noncomputable def IndexedLOrder.isTypedNC (i : I) (σ : Finset T) (C : Finset I): Prop := IST.isCell σ C ∧ (C \ (σ.image c)) = {i}

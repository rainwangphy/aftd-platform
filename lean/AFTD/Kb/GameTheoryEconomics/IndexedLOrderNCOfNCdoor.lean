import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IndexedLOrder
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsTypedNC
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsDoorof
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsColorful
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderNCOrCOfDoor
import AFTD.Kb.GameTheoryEconomics.InstFunLikeIndexedLOrderLinearOrder

/-!
# IndexedLOrder.NC_of_NCdoor

Topic: general_equilibrium   Node: f2af6dc265ff

Provenance: formalization of a published result. Source: EconCSLib, `IndexedLOrder.NC_of_NCdoor`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Scarf.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

IndexedLOrder.NC_of_NCdoor
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
variable {c σ C} in
variable [Fintype T] [Fintype I] in
variable (c) in
omit [Fintype T] [Fintype I] [Inhabited T] in
variable {c} in
lemma IndexedLOrder.NC_of_NCdoor (h1 : isTypedNC c i τ D)
(h2 : isDoorof τ D σ C) :
  ¬ isColorful c σ C → isTypedNC c i σ C := by
  intro h_not_colorful
  obtain h_typed | h_colorful := NC_or_C_of_door h1 h2
  · exact h_typed
  · contradiction

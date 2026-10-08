import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IndexedLOrder
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsOutsideDoor
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsNearlyColorful
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsDoor
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsCell
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsDominant
import AFTD.Kb.GameTheoryEconomics.InstFunLikeIndexedLOrderLinearOrder

/-!
# IndexedLOrder.NC_of_outsidedoor

Topic: general_equilibrium   Node: 3f6c9618a565

Provenance: formalization of a published result. Source: EconCSLib, `IndexedLOrder.NC_of_outsidedoor`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Scarf.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

IndexedLOrder.NC_of_outsidedoor
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
omit [Inhabited T] [DecidableEq T] in
lemma IndexedLOrder.NC_of_outsidedoor (h : isOutsideDoor σ C) : isNearlyColorful c σ C := by
  cases h with
  | intro hd he =>
    unfold isNearlyColorful
    unfold isCell
    constructor
    · exact hd.1
    · rw [he]
      have h_img : Finset.image c Finset.empty = Finset.empty := Finset.image_empty c
      rw [h_img]
      have h_disj : Disjoint C Finset.empty := Finset.disjoint_empty_right C
      have h_sdiff : C \ Finset.empty = C := Finset.sdiff_eq_self_of_disjoint h_disj
      rw [h_sdiff]
      unfold isDoor at hd
      have h1 := hd.2
      rw [he] at h1
      exact h1

/-Lemma 5-/

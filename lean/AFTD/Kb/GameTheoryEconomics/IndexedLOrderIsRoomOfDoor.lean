import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IndexedLOrder
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsDoorof
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsRoom
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsCell
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsDoor
import AFTD.Kb.GameTheoryEconomics.InstFunLikeIndexedLOrderLinearOrder

/-!
# IndexedLOrder.isRoom_of_Door

Topic: general_equilibrium   Node: b6a225bc8f1c

Provenance: formalization of a published result. Source: EconCSLib, `IndexedLOrder.isRoom_of_Door`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Scarf.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

IndexedLOrder.isRoom_of_Door
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
variable {σ C} in
omit [Inhabited T] in
lemma IndexedLOrder.isRoom_of_Door (h1 : isDoorof τ D σ C) : IST.isRoom σ C := by
  cases h1
  · rename_i h0 h2 x h3 h4 h5
    constructor
    · exact h0
    · simp only [<-h5, h2.2, <-h4, h3, not_false_eq_true, Finset.card_insert_of_notMem]
  · rename_i h0 h2 x h3 h4 h5
    constructor
    · exact h0
    · have h6 := Finset.card_insert_of_notMem h3
      subst h4
      replace h5 : D.card = (insert x C).card := by rw [h5]
      rw [h6] at h5
      rw [h2.2] at h5
      exact Eq.symm $ (add_left_inj _).1 h5

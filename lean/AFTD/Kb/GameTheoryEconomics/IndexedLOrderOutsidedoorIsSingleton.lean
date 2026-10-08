import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IndexedLOrder
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsOutsideDoor
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsDoor
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsCell
import AFTD.Kb.GameTheoryEconomics.InstFunLikeIndexedLOrderLinearOrder

/-!
# IndexedLOrder.outsidedoor_is_singleton

Topic: general_equilibrium   Node: e386e226b1be

Provenance: formalization of a published result. Source: EconCSLib, `IndexedLOrder.outsidedoor_is_singleton`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Scarf.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

IndexedLOrder.outsidedoor_is_singleton
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
omit [Inhabited T] [DecidableEq T] [DecidableEq I] in
lemma IndexedLOrder.outsidedoor_is_singleton (h : IST.isOutsideDoor τ  D) :  τ = Finset.empty ∧  ∃ i, D = {i} := by
  obtain ⟨h1, h2⟩ := h
  subst h2
  obtain ⟨_,h3⟩ := h1
  replace h4 : D.card = 1 := by
    simp_all
    rfl
  exact ⟨rfl, Finset.card_eq_one.1 h4⟩

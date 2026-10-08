import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IndexedLOrder
import AFTD.Kb.GameTheoryEconomics.InstFunLikeIndexedLOrderLinearOrder

/-!
# IndexedLOrder.Finset.eq_of_mem_of_card_one

Topic: general_equilibrium   Node: 491a00131add

Provenance: formalization of a published result. Source: EconCSLib, `IndexedLOrder.Finset.eq_of_mem_of_card_one`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Scarf.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

IndexedLOrder.Finset.eq_of_mem_of_card_one
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
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
lemma IndexedLOrder.Finset.eq_of_mem_of_card_one {X : Type*} [DecidableEq X] {s : Finset X} {a : X} (h_mem : a ∈ s) (h_card : s.card = 1) : s = {a} :=
  Finset.eq_singleton_iff_unique_mem.mpr ⟨h_mem, fun y hy =>
    let ⟨b, hb⟩ := Finset.card_eq_one.mp h_card
    have h_a_eq_b : a = b := Finset.eq_of_mem_singleton (hb ▸ h_mem)
    have h_y_eq_b : y = b := Finset.eq_of_mem_singleton (hb ▸ hy)
    h_y_eq_b.trans h_a_eq_b.symm⟩

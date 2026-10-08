import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IndexedLOrder
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsTypedNC
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsColorful
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsCell
import AFTD.Kb.GameTheoryEconomics.InstFunLikeIndexedLOrderLinearOrder

/-!
# IndexedLOrder.not_colorful_of_TypedNC

Topic: general_equilibrium   Node: c47422ea86de

Provenance: formalization of a published result. Source: EconCSLib, `IndexedLOrder.not_colorful_of_TypedNC`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Scarf.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

IndexedLOrder.not_colorful_of_TypedNC
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
lemma IndexedLOrder.not_colorful_of_TypedNC (h1 : isTypedNC c i σ C) : ¬ IST.isColorful c σ C := by
  intro h
  unfold isTypedNC at h1
  unfold isColorful at h
  have h_diff := h1.2
  have h_ne : σ.image c ≠ C := by
    intro h_eq
    rw [←h_eq, Finset.sdiff_self] at h_diff
    have h_singleton_nonempty : ({i} : Finset I).Nonempty := Finset.singleton_nonempty i
    rw [←h_diff] at h_singleton_nonempty
    exact Finset.not_nonempty_empty h_singleton_nonempty
  exact h_ne h.2

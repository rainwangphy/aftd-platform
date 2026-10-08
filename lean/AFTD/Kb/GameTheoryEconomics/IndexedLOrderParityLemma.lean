import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IndexedLOrder
import AFTD.Kb.GameTheoryEconomics.InstFunLikeIndexedLOrderLinearOrder

/-!
# IndexedLOrder.parity_lemma

Topic: general_equilibrium   Node: 001d057263ba

Provenance: formalization of a published result. Source: EconCSLib, `IndexedLOrder.parity_lemma`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Scarf.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

IndexedLOrder.parity_lemma
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
variable [Fintype T] [Fintype I] in
variable (c) in
lemma IndexedLOrder.parity_lemma {a b c d : ℕ } (h1 : Odd a) (h2 : Even b) (h3 : Even d) (h4 : a + b = c + d ): Odd c := by
  by_contra h0
  replace h0 := Nat.not_odd_iff_even.1 h0
  have oddab := Even.odd_add h2 h1
  rw [h4] at oddab
  have evencd := Even.add h0 h3
  exact Nat.not_odd_iff_even.2 evencd oddab

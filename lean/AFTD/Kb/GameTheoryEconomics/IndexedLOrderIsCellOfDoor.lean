import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IndexedLOrder
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsDoorof
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsCell
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsDoor
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderDominantOfSubset
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderDominantOfSupset
import AFTD.Kb.GameTheoryEconomics.InstFunLikeIndexedLOrderLinearOrder

/-!
# IndexedLOrder.isCell_of_door

Topic: general_equilibrium   Node: 0f06f0690060

Provenance: formalization of a published result. Source: EconCSLib, `IndexedLOrder.isCell_of_door`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Scarf.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

IndexedLOrder.isCell_of_door
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
omit [Inhabited T] in
lemma IndexedLOrder.isCell_of_door (h1 : isDoorof τ D σ C) : IST.isCell τ D := by
  cases h1
  · rename_i h0 _ j h1 h3 h4
    rw [h4]
    exact IST.Dominant_of_subset _ _ C (by simp [<-h3]) h0
  · rename_i h0 _ j h1 h2' h3
    rw [h2', h3]
    exact IST.Dominant_of_supset _ _ _ (Finset.subset_insert j C) h0

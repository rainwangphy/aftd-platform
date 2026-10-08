import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IndexedLOrder
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsCell
import AFTD.Kb.GameTheoryEconomics.InstFunLikeIndexedLOrderLinearOrder

/-!
# IndexedLOrder.isColorful

Topic: general_equilibrium   Node: 5586d7299c27

Provenance: formalization of a published result. Source: EconCSLib, `IndexedLOrder.isColorful`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Scarf.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`(σ, C)` is **colorful** under coloring `c : T → I`: it is a dominant cell and the coloring `c` maps `σ` **bijectively** onto `C` (i.e., `σ.image c = C`). A colorful room is the central object of Scarf's lemma: its existence is guaranteed for every coloring `c`.
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
/-- `(σ, C)` is **colorful** under coloring `c : T → I`: it is a dominant cell and the coloring `c` maps `σ` **bijectively** onto `C` (i.e., `σ.image c = C`). A colorful room is the central object of Scarf's lemma: its existence is guaranteed for every coloring `c`. -/
noncomputable def IndexedLOrder.isColorful : Prop := IST.isCell σ C ∧ σ.image c   = C

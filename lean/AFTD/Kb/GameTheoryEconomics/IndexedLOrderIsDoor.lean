import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IndexedLOrder
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsCell
import AFTD.Kb.GameTheoryEconomics.InstFunLikeIndexedLOrderLinearOrder

/-!
# IndexedLOrder.isDoor

Topic: general_equilibrium   Node: 2184a114889d

Provenance: formalization of a published result. Source: EconCSLib, `IndexedLOrder.isDoor`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Scarf.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`(σ, C)` is a **door**: a dominant cell with `|C| = |σ| + 1`. A door has one more color than points; it is adjacent to exactly two rooms in the Scarf complex. Doors are the "walls" between rooms in the parity argument.
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
/-- `(σ, C)` is a **door**: a dominant cell with `|C| = |σ| + 1`. A door has one more color than points; it is adjacent to exactly two rooms in the Scarf complex. Doors are the "walls" between rooms in the parity argument. -/
abbrev IndexedLOrder.isDoor :=  isCell σ C ∧ C.card = σ.card + 1

import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GSPreferences
import AFTD.Kb.GameTheoryEconomics.GSGs
import AFTD.Kb.GameTheoryEconomics.GsInjective

/-!
# gs_bijective

Topic: matching_markets   Node: f42352b8c345

Provenance: formalization of a published result. Source: EconCSLib, `gs_bijective`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MarketDesign/Matching/GaleShapley.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`gs w m` is a bijection on `Fin n`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open List Finset in
open GS in
variable {n : ℕ} [NeZero n] in
variable (w m : Preferences n) in
/-- `gs w m` is a bijection on `Fin n`. -/
lemma gs_bijective : Function.Bijective (gs w m) :=
  Finite.injective_iff_bijective.mp (gs_injective w m)

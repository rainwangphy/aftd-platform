import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OpponentProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsert
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertSelf

/-!
# BayesianSingleItemAuction.profileInsert_of_ne

Topic: mechanism_design   Node: 52996d8508bb

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.profileInsert_of_ne`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Other coordinates come from the opponent profile.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
variable {I : Type*} in
variable {X : Type*} in
/-- Other coordinates come from the opponent profile. -/
@[simp] theorem BayesianSingleItemAuction.profileInsert_of_ne
    (i : I) (x : X) (t : OpponentProfile I X i) {j : I} (hji : j ≠ i) :
    profileInsert i x t j = t ⟨j, hji⟩ := by
  simp [profileInsert, hji]

import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OpponentProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsert

/-!
# BayesianSingleItemAuction.profileInsert_self

Topic: mechanism_design   Node: 31e7c262f95f

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.profileInsert_self`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The inserted coordinate is the inserted value.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
variable {I : Type*} in
variable {X : Type*} in
/-- The inserted coordinate is the inserted value. -/
@[simp] theorem BayesianSingleItemAuction.profileInsert_self (i : I) (x : X) (t : OpponentProfile I X i) :
    profileInsert i x t i = x := by
  simp [profileInsert]

import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OpponentTypeProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionReportProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertOfNe

/-!
# BayesianSingleItemAuction.reportProfile_self

Topic: mechanism_design   Node: e7300d0f19c2

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.reportProfile_self`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The inserted coordinate is `zᵢ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
variable {I : Type*} in
/-- The inserted coordinate is `zᵢ`. -/
@[simp] theorem BayesianSingleItemAuction.reportProfile_self (i : I) (z_i : ℝ) (t : OpponentTypeProfile I i) :
    reportProfile i z_i t i = z_i := by
  simp [reportProfile]

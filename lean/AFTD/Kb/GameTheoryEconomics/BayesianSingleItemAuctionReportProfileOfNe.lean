import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OpponentTypeProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionReportProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionReportProfileSelf

/-!
# BayesianSingleItemAuction.reportProfile_of_ne

Topic: mechanism_design   Node: 89d070bb480d

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.reportProfile_of_ne`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Other coordinates come from the opponent profile.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
variable {I : Type*} in
/-- Other coordinates come from the opponent profile. -/
@[simp] theorem BayesianSingleItemAuction.reportProfile_of_ne
    (i : I) (z_i : ℝ) (t : OpponentTypeProfile I i) {j : I} (hji : j ≠ i) :
    reportProfile i z_i t j = t ⟨j, hji⟩ := by
  simp [reportProfile, hji]

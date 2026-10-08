import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OpponentTypeProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionReportProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionReportProfileSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionReportProfileOfNe
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertOfNe

/-!
# BayesianSingleItemAuction.update_reportProfile_self

Topic: mechanism_design   Node: 88c0ec6be6e2

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.update_reportProfile_self`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Updating coordinate `i` replaces the inserted report.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
variable {I : Type*} in
/-- Updating coordinate `i` replaces the inserted report. -/
@[simp] theorem BayesianSingleItemAuction.update_reportProfile_self
    [DecidableEq I] (i : I) (z_i y_i : ℝ) (t : OpponentTypeProfile I i) :
    Function.update (reportProfile i z_i t) i y_i = reportProfile i y_i t := by
  funext j
  by_cases hji : j = i
  · subst hji
    simp
  · simp [hji]

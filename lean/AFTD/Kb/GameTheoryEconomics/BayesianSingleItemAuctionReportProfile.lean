import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OpponentTypeProfile
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsert
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertSelf
import AFTD.Kb.GameTheoryEconomics.BayesianSingleItemAuctionProfileInsertOfNe

/-!
# BayesianSingleItemAuction.reportProfile

Topic: mechanism_design   Node: a0f49f4fabbb

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.reportProfile`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The reported type profile obtained by combining `zᵢ` with an opponent profile `t₋ᵢ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
variable {I : Type*} in
/-- The reported type profile obtained by combining `zᵢ` with an opponent profile `t₋ᵢ`. -/
noncomputable def BayesianSingleItemAuction.reportProfile (i : I) (z_i : ℝ) (t : OpponentTypeProfile I i) :
    ∀ _ : I, ℝ :=
  profileInsert i z_i t

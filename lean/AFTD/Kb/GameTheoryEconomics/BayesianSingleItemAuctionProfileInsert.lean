import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OpponentProfile

/-!
# BayesianSingleItemAuction.profileInsert

Topic: mechanism_design   Node: 9ebbc047fd08

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.profileInsert`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Insert one coordinate into an opponent profile.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
variable {I : Type*} in
variable {X : Type*} in
/-- Insert one coordinate into an opponent profile. -/
noncomputable def BayesianSingleItemAuction.profileInsert (i : I) (x : X) (t : OpponentProfile I X i) :
    ∀ _ : I, X := by
  classical
  exact fun j => if h : j = i then x else t ⟨j, h⟩

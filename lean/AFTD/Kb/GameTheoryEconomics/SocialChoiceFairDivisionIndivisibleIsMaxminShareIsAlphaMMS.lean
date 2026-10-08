import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleIsAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleIsMaxminShare
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleMmsValue
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleIsAlphaMMS
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleIsAlphaMMSMonoAlpha
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleIsMaxminShareIffIsAlphaMMSOne

/-!
# SocialChoice.FairDivision.Indivisible.IsMaxminShare.isAlphaMMS

Topic: fair_division   Node: 5faa77f201e4

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.IsMaxminShare.isAlphaMMS`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/MMS.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**`IsMaxminShare` implies α-MMS** for `α ≤ 1` and nonneg MMS values.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N G : Type*} in
variable [Fintype N] [DecidableEq G] in
/-- **`IsMaxminShare` implies α-MMS** for `α ≤ 1` and nonneg MMS values. -/
theorem SocialChoice.FairDivision.Indivisible.IsMaxminShare.isAlphaMMS
    [Nonempty N] [Fintype G]
    (v : Valuation N G) (allGoods : Finset G) (A : Allocation N G)
    (hne : Nonempty {A' : Allocation N G // IsAllocation allGoods A'})
    (hMMS : IsMaxminShare v allGoods A)
    (α : ℝ) (hα_le : α ≤ 1)
    (hmms_nn : ∀ i, 0 ≤ mmsValue v allGoods i) :
    IsAlphaMMS α v allGoods A :=
  isAlphaMMS_mono_alpha v allGoods A 1 α hα_le hmms_nn
    ((isMaxminShare_iff_isAlphaMMS_one v allGoods A hne).mp hMMS)

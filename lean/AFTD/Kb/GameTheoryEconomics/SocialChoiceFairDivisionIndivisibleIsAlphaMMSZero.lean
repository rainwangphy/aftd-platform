import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleIsAlphaMMS
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleMmsValue

/-!
# SocialChoice.FairDivision.Indivisible.isAlphaMMS_zero

Topic: fair_division   Node: 58e36f691d62

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.isAlphaMMS_zero`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/MMS.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Every allocation trivially satisfies **0-MMS** for nonneg valuations. `0 * mmsValue = 0 ≤ v_i(A_i)` by `zero_mul` and nonnegativity.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N G : Type*} in
variable [Fintype N] [DecidableEq G] in
/-- Every allocation trivially satisfies **0-MMS** for nonneg valuations. `0 * mmsValue = 0 ≤ v_i(A_i)` by `zero_mul` and nonnegativity. -/
theorem SocialChoice.FairDivision.Indivisible.isAlphaMMS_zero
    (v : Valuation N G) (allGoods : Finset G) (A : Allocation N G)
    (hnonneg : ∀ i S, 0 ≤ v.val i S) :
    IsAlphaMMS 0 v allGoods A := by
  intro i
  show 0 * mmsValue v allGoods i ≤ v.val i (A i)
  rw [zero_mul]
  exact hnonneg i (A i)

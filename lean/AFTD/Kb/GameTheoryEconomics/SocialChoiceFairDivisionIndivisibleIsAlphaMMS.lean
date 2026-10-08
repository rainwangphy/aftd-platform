import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleMmsValue

/-!
# SocialChoice.FairDivision.Indivisible.IsAlphaMMS

Topic: fair_division   Node: 31eddb5f9c9f

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.IsAlphaMMS`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/MMS.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An allocation `A` is **α-MMS** if every agent receives at least `α` times their MMS value. `IsAlphaMMS α v allGoods A ↔ ∀ i, α * mmsValue v allGoods i ≤ v.val i (A i)`. The scalar `α : ℝ` quantifies approximation quality: - `α = 1`: full MMS, equivalent to `IsMaxminShare` from `Fairness.lean` (see `isMaxminShare_iff_isAlphaMMS_one`). - `α = 3/4`: always achievable for additive valuations (see `exists_isAlphaMMS_threefourths`). - `α = 0`: trivially satisfied for nonneg valuations (see `isAlphaMMS_zero`). [Budish 2011; Amanatidis et al. 2017; Garg-Taki 2021]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N G : Type*} in
/-- An allocation `A` is **α-MMS** if every agent receives at least `α` times their MMS value. `IsAlphaMMS α v allGoods A ↔ ∀ i, α * mmsValue v allGoods i ≤ v.val i (A i)`. The scalar `α : ℝ` quantifies approximation quality: - `α = 1`: full MMS, equivalent to `IsMaxminShare` from `Fairness.lean` (see `isMaxminShare_iff_isAlphaMMS_one`). - `α = 3/4`: always achievable for additive valuations (see `exists_isAlphaMMS_threefourths`). - `α = 0`: trivially satisfied for nonneg valuations (see `isAlphaMMS_zero`). [Budish 2011; Amanatidis et al. 2017; Garg-Taki 2021] -/
def SocialChoice.FairDivision.Indivisible.IsAlphaMMS [Fintype N] [DecidableEq G]
    (α : ℝ) (v : Valuation N G) (allGoods : Finset G) (A : Allocation N G) : Prop :=
  ∀ i : N, α * mmsValue v allGoods i ≤ v.val i (A i)

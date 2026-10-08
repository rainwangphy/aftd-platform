import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleMmsValue
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleIsAlphaMMS

/-!
# SocialChoice.FairDivision.Indivisible.isAlphaMMS_mono_alpha

Topic: fair_division   Node: 88e660f507fc

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.isAlphaMMS_mono_alpha`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/MMS.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**α-MMS is monotone decreasing in α**: if `A` is α-MMS and `β ≤ α`, then `A` is β-MMS. *Proof*: `β * mmsValue ≤ α * mmsValue ≤ v_i(A_i)` since `β ≤ α` and `mmsValue ≥ 0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N G : Type*} in
variable [Fintype N] [DecidableEq G] in
/-- **α-MMS is monotone decreasing in α**: if `A` is α-MMS and `β ≤ α`, then `A` is β-MMS. *Proof*: `β * mmsValue ≤ α * mmsValue ≤ v_i(A_i)` since `β ≤ α` and `mmsValue ≥ 0`. -/
theorem SocialChoice.FairDivision.Indivisible.isAlphaMMS_mono_alpha
    (v : Valuation N G) (allGoods : Finset G) (A : Allocation N G)
    (α β : ℝ) (hβα : β ≤ α)
    (hmms_nn : ∀ i, 0 ≤ mmsValue v allGoods i)
    (hα : IsAlphaMMS α v allGoods A) :
    IsAlphaMMS β v allGoods A := by
  intro i
  calc β * mmsValue v allGoods i
      ≤ α * mmsValue v allGoods i := mul_le_mul_of_nonneg_right hβα (hmms_nn i)
    _ ≤ v.val i (A i)             := hα i

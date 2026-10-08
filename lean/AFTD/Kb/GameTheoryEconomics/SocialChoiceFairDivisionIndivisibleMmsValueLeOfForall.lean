import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleIsAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleMmsValue

/-!
# SocialChoice.FairDivision.Indivisible.mmsValue_le_of_forall

Topic: fair_division   Node: 721088d8fd2d

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.mmsValue_le_of_forall`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/MMS.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The MMS value is at most any upper bound on all per-allocation minimum bundle values. If `ub` is an upper bound — for every complete allocation `B`, `iInf_j v_i(B_j) ≤ ub` — then `mmsValue v allGoods i ≤ ub`. `hne` is needed because `ciSup_le` requires the index type to be nonempty.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N G : Type*} in
variable [Fintype N] [DecidableEq G] in
/-- The MMS value is at most any upper bound on all per-allocation minimum bundle values. If `ub` is an upper bound — for every complete allocation `B`, `iInf_j v_i(B_j) ≤ ub` — then `mmsValue v allGoods i ≤ ub`. `hne` is needed because `ciSup_le` requires the index type to be nonempty. -/
lemma SocialChoice.FairDivision.Indivisible.mmsValue_le_of_forall
    (v : Valuation N G) (allGoods : Finset G) (i : N)
    (hne : Nonempty {A : Allocation N G // IsAllocation allGoods A})
    (ub : ℝ)
    (h : ∀ B : Allocation N G, IsAllocation allGoods B →
        iInf (fun j : N => v.val i (B j)) ≤ ub) :
    mmsValue v allGoods i ≤ ub := by
  haveI : Nonempty {A : Allocation N G // IsAllocation allGoods A} := hne
  exact ciSup_le fun ⟨B, hB⟩ => h B hB

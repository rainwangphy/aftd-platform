import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleIsAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleMmsValue

/-!
# SocialChoice.FairDivision.Indivisible.iInf_partition_le_mmsValue

Topic: fair_division   Node: d5deab2b256c

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.iInf_partition_le_mmsValue`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/MMS.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The min-bundle value of any complete allocation is at most the MMS value. For any complete allocation `B`: `iInf_{j : N} v_i(B_j) ≤ mmsValue v allGoods i`. Requires `BddAbove` of the range of all per-allocation minimums, which holds when `[Fintype G]` (finitely many partitions). [Budish 2011]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N G : Type*} in
variable [Fintype N] [DecidableEq G] in
/-- The min-bundle value of any complete allocation is at most the MMS value. For any complete allocation `B`: `iInf_{j : N} v_i(B_j) ≤ mmsValue v allGoods i`. Requires `BddAbove` of the range of all per-allocation minimums, which holds when `[Fintype G]` (finitely many partitions). [Budish 2011] -/
lemma SocialChoice.FairDivision.Indivisible.iInf_partition_le_mmsValue
    (v : Valuation N G) (allGoods : Finset G) (i : N)
    (B : Allocation N G) (hB : IsAllocation allGoods B)
    (hbdd : BddAbove (Set.range fun X : {A : Allocation N G // IsAllocation allGoods A} =>
        iInf fun j : N => v.val i (X.val j))) :
    iInf (fun j : N => v.val i (B j)) ≤ mmsValue v allGoods i :=
  le_ciSup hbdd ⟨B, hB⟩

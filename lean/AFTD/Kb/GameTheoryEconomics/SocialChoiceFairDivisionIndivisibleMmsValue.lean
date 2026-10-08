import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleIsAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation

/-!
# SocialChoice.FairDivision.Indivisible.mmsValue

Topic: fair_division   Node: d301fad146d2

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.mmsValue`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/MMS.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The **maximin share (MMS) value** of agent `i` with respect to valuation `v` and good set `allGoods`. `mmsValue v allGoods i = sup_{B : n-partition} inf_{j : N} v_i(B_j)`. Intuitively: the best (highest) minimum-bundle value agent `i` can guarantee by proposing a complete `n`-partition of `allGoods`. The outer `iSup` ranges over all complete allocations `{B // IsAllocation allGoods B}`; the inner `iInf` ranges over all agent indices `j : N` (the bundle labels). The corresponding **predicate** ("did agent `i` receive at least their MMS value?") is `IsMaxminShare` in `Fairness.lean`. See `isMaxminShare_iff_isAlphaMMS_one` for the connection. If no complete allocation exists (e.g., `N = ∅`), `iSup` over the empty subtype yields `sSup ∅ = 0` in ℝ. Use `[Nonempty N]` to ensure a complete allocation exists. [Budish 2011; AGT Ch.11]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N G : Type*} in
/-- The **maximin share (MMS) value** of agent `i` with respect to valuation `v` and good set `allGoods`. `mmsValue v allGoods i = sup_{B : n-partition} inf_{j : N} v_i(B_j)`. Intuitively: the best (highest) minimum-bundle value agent `i` can guarantee by proposing a complete `n`-partition of `allGoods`. The outer `iSup` ranges over all complete allocations `{B // IsAllocation allGoods B}`; the inner `iInf` ranges over all agent indices `j : N` (the bundle labels). The corresponding **predicate** ("did agent `i` receive at least their MMS value?") is `IsMaxminShare` in `Fairness.lean`. See `isMaxminShare_iff_isAlphaMMS_one` for the connection. If no complete allocation exists (e.g., `N = ∅`), `iSup` over the empty subtype yields `sSup ∅ = 0` in ℝ. Use `[Nonempty N]` to ensure a complete allocation exists. [Budish 2011; AGT Ch.11] -/
noncomputable def SocialChoice.FairDivision.Indivisible.mmsValue [Fintype N] [DecidableEq G]
    (v : Valuation N G) (allGoods : Finset G) (i : N) : ℝ :=
  iSup fun B : {A : Allocation N G // IsAllocation allGoods A} =>
    iInf fun j : N => v.val i (B.val j)

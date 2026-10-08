import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleIsAllocation

/-!
# SocialChoice.FairDivision.Indivisible.IsMaxminShare

Topic: fair_division   Node: 8f3d54c8d141

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.IsMaxminShare`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/Fairness.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Maximin share (MMS) guarantee: each agent's bundle is at least as valuable as their maximin share value — the best worst-piece they could guarantee by self-partitioning. Formally: for each agent `i`, for every complete allocation `B` of `allGoods`, some bundle in `B` has value ≤ `v_i(A_i)` (agent `i`'s bundle in `A`). This is equivalent to the standard MMS definition: `v_i(A_i) ≥ MMS_i` where `MMS_i = max_{B complete} min_j v_i(B_j)` (the maximum over all complete `n`-partitions of the minimum bundle value for agent `i`). The equivalence holds because `∀ B, ∃ j, v_i(B_j) ≤ v_i(A_i)` is the same as `∀ B, min_j v_i(B_j) ≤ v_i(A_i)`, i.e., `v_i(A_i) ≥ max_B min_j v_i(B_j)`. This formulation avoids `iSup`/`iInf` and is stated directly in the real-valued order. MMS is the weakest standard fairness guarantee in the hierarchy: `EF → EFX → EF1 → PROP → MMS` (for additive normalized valuations). Key results: - `IsProportional.isMaxminShare` (in `Implications`): PROP implies MMS. - MMS allocations almost always exist for additive preferences (Bouveret-Lemaître 2014). - MMS allocations need not always exist (Procaccia-Wang 2014 counterexample). - At least (3/4)-MMS is always achievable for additive preferences. `[Fintype N]` and `[DecidableEq G]` are required by `IsAllocation`. [BCM Ch.12; Budish 2011]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N G : Type*} in
/-- Maximin share (MMS) guarantee: each agent's bundle is at least as valuable as their maximin share value — the best worst-piece they could guarantee by self-partitioning. Formally: for each agent `i`, for every complete allocation `B` of `allGoods`, some bundle in `B` has value ≤ `v_i(A_i)` (agent `i`'s bundle in `A`). This is equivalent to the standard MMS definition: `v_i(A_i) ≥ MMS_i` where `MMS_i = max_{B complete} min_j v_i(B_j)` (the maximum over all complete `n`-partitions of the minimum bundle value for agent `i`). The equivalence holds because `∀ B, ∃ j, v_i(B_j) ≤ v_i(A_i)` is the same as `∀ B, min_j v_i(B_j) ≤ v_i(A_i)`, i.e., `v_i(A_i) ≥ max_B min_j v_i(B_j)`. This formulation avoids `iSup`/`iInf` and is stated directly in the real-valued order. MMS is the weakest standard fairness guarantee in the hierarchy: `EF → EFX → EF1 → PROP → MMS` (for additive normalized valuations). Key results: - `IsProportional.isMaxminShare` (in `Implications`): PROP implies MMS. - MMS allocations almost always exist for additive preferences (Bouveret-Lemaître 2014). - MMS allocations need not always exist (Procaccia-Wang 2014 counterexample). - At least (3/4)-MMS is always achievable for additive preferences. `[Fintype N]` and `[DecidableEq G]` are required by `IsAllocation`. [BCM Ch.12; Budish 2011] -/
def SocialChoice.FairDivision.Indivisible.IsMaxminShare [Fintype N] [DecidableEq G]
    (v : Valuation N G) (allGoods : Finset G) (A : Allocation N G) : Prop :=
  ∀ i : N, ∀ B : Allocation N G, IsAllocation allGoods B →
    ∃ j : N, v.val i (B j) ≤ v.val i (A i)

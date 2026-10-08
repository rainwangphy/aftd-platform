import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIsMaxmin
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleIsAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique

/-!
# SocialChoice.FairDivision.Indivisible.IsMaxmin

Topic: fair_division   Node: d6244eaf0a74

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.IsMaxmin`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/SocialWelfare.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Maximin (egalitarian) optimal: no complete allocation of `allGoods` achieves higher egalitarian (minimum-agent) welfare. A maximin allocation makes the worst-off agent as well off as possible. This is the egalitarian counterpart to utilitarian optimality, and is distinct from the per-agent maximin share guarantee (`IsMaxminShare` in `Fairness.lean`): - `IsMaxmin` is a global property: it is the best possible for the social minimum. - `IsMaxminShare` is per-agent: each agent individually gets at least their MMS value. `[Nonempty N]` ensures `egalitarianWelfare` is well-defined. [BCM Ch.12, Def 12.6]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators Finset in
variable {N G : Type*} in
/-- Maximin (egalitarian) optimal: no complete allocation of `allGoods` achieves higher egalitarian (minimum-agent) welfare. A maximin allocation makes the worst-off agent as well off as possible. This is the egalitarian counterpart to utilitarian optimality, and is distinct from the per-agent maximin share guarantee (`IsMaxminShare` in `Fairness.lean`): - `IsMaxmin` is a global property: it is the best possible for the social minimum. - `IsMaxminShare` is per-agent: each agent individually gets at least their MMS value. `[Nonempty N]` ensures `egalitarianWelfare` is well-defined. [BCM Ch.12, Def 12.6] -/
abbrev SocialChoice.FairDivision.Indivisible.IsMaxmin [Fintype N] [Nonempty N] [DecidableEq G]
    (v : Valuation N G) (allGoods : Finset G) (A : Allocation N G) : Prop :=
  SocialChoice.FairDivision.IsMaxmin (fun B => IsAllocation allGoods B) v.val A

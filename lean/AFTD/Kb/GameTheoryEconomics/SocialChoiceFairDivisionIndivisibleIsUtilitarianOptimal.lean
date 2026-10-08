import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIsUtilitarianOptimal
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleIsAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique

/-!
# SocialChoice.FairDivision.Indivisible.IsUtilitarianOptimal

Topic: fair_division   Node: 5d5971be81da

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.IsUtilitarianOptimal`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/SocialWelfare.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Utilitarian optimal: no complete allocation of `allGoods` achieves strictly higher utilitarian (sum) social welfare. `[Fintype N] [DecidableEq G]` are required by `IsAllocation`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators Finset in
variable {N G : Type*} in
/-- Utilitarian optimal: no complete allocation of `allGoods` achieves strictly higher utilitarian (sum) social welfare. `[Fintype N] [DecidableEq G]` are required by `IsAllocation`. -/
abbrev SocialChoice.FairDivision.Indivisible.IsUtilitarianOptimal [Fintype N] [DecidableEq G]
    (v : Valuation N G) (allGoods : Finset G) (A : Allocation N G) : Prop :=
  SocialChoice.FairDivision.IsUtilitarianOptimal (fun B => IsAllocation allGoods B) v.val A

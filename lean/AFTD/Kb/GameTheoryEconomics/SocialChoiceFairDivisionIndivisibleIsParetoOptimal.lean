import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIsParetoOptimal
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleIsAllocation

/-!
# SocialChoice.FairDivision.Indivisible.IsParetoOptimal

Topic: fair_division   Node: 6b0119a6daeb

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.IsParetoOptimal`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/Efficiency.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An allocation `A` is Pareto optimal if no complete allocation `B` weakly improves every agent's bundle value and strictly improves at least one agent's value. `[Fintype N]` is required because `IsAllocation` uses `Finset.univ.biUnion`. `[DecidableEq G]` is required for `Finset` operations. [AGT Ch.12]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N G : Type*} in
/-- An allocation `A` is Pareto optimal if no complete allocation `B` weakly improves every agent's bundle value and strictly improves at least one agent's value. `[Fintype N]` is required because `IsAllocation` uses `Finset.univ.biUnion`. `[DecidableEq G]` is required for `Finset` operations. [AGT Ch.12] -/
abbrev SocialChoice.FairDivision.Indivisible.IsParetoOptimal [Fintype N] [DecidableEq G]
    (v : Valuation N G) (allGoods : Finset G) (A : Allocation N G) : Prop :=
  SocialChoice.FairDivision.IsParetoOptimal (fun B => IsAllocation allGoods B) v.val A

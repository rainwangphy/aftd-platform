import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionEgalitarianWelfare
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique
import AFTD.Kb.Tcs.G

/-!
# SocialChoice.FairDivision.Indivisible.egalitarianWelfare

Topic: fair_division   Node: efb12ec7d866

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.egalitarianWelfare`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/SocialWelfare.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Egalitarian social welfare: the minimum of all agents' bundle values. `sw_E(A) = min_{i ∈ N} v_i(A_i)`. Maximizing egalitarian welfare yields the *maximin* allocation: it makes the worst-off agent as well off as possible. For this to be meaningful, agent valuations should be comparable (e.g., all normalized to total value 1 over all goods). Requires `[Fintype N] [Nonempty N]` so the minimum is taken over a nonempty set. [BCM Ch.12, Def 12.6]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators Finset in
variable {N G : Type*} in
/-- Egalitarian social welfare: the minimum of all agents' bundle values. `sw_E(A) = min_{i ∈ N} v_i(A_i)`. Maximizing egalitarian welfare yields the *maximin* allocation: it makes the worst-off agent as well off as possible. For this to be meaningful, agent valuations should be comparable (e.g., all normalized to total value 1 over all goods). Requires `[Fintype N] [Nonempty N]` so the minimum is taken over a nonempty set. [BCM Ch.12, Def 12.6] -/
noncomputable abbrev SocialChoice.FairDivision.Indivisible.egalitarianWelfare [Fintype N] [Nonempty N]
    (v : Valuation N G) (A : Allocation N G) : ℝ :=
  SocialChoice.FairDivision.egalitarianWelfare v.val A

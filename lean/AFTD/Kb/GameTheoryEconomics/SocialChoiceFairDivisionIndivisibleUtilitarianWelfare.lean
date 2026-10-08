import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfare
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionUtilitarianWelfareUnique

/-!
# SocialChoice.FairDivision.Indivisible.utilitarianWelfare

Topic: fair_division   Node: b0c54abeba92

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.utilitarianWelfare`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/SocialWelfare.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Utilitarian social welfare: the sum of all agents' bundle values. `sw_U(A) = ∑_{i ∈ N} v_i(A_i)`. Maximizing utilitarian welfare produces *utilitarian optimal* allocations — generally not fair, since all value may concentrate on one agent. The ratio between utilitarian optimal welfare and the welfare of the best fair allocation is the *price of fairness*. Requires `[Fintype N]` to sum over all agents. [BCM Ch.12]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BigOperators Finset in
variable {N G : Type*} in
/-- Utilitarian social welfare: the sum of all agents' bundle values. `sw_U(A) = ∑_{i ∈ N} v_i(A_i)`. Maximizing utilitarian welfare produces *utilitarian optimal* allocations — generally not fair, since all value may concentrate on one agent. The ratio between utilitarian optimal welfare and the welfare of the best fair allocation is the *price of fairness*. Requires `[Fintype N]` to sum over all agents. [BCM Ch.12] -/
noncomputable abbrev SocialChoice.FairDivision.Indivisible.utilitarianWelfare [Fintype N]
    (v : Valuation N G) (A : Allocation N G) : ℝ :=
  SocialChoice.FairDivision.utilitarianWelfare v.val A

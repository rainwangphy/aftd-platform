import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAllocation

/-!
# SocialChoice.FairDivision.Indivisible.isEnvyFree

Topic: fair_division   Node: 49052cc5a7f2

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.isEnvyFree`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/Checker.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Noncomputable envy-free Boolean reflection helper. Returns `true` iff `A` is envy-free under valuation `v`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N G : Type*} in
/-- Noncomputable envy-free Boolean reflection helper. Returns `true` iff `A` is envy-free under valuation `v`. -/
noncomputable def SocialChoice.FairDivision.Indivisible.isEnvyFree [Fintype N]
    (v : Valuation N G) (A : Allocation N G) : Bool :=
  decide (∀ i j : N, v.val i (A j) ≤ v.val i (A i))

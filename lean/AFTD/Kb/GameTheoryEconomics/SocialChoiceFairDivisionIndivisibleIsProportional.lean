import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAllocation

/-!
# SocialChoice.FairDivision.Indivisible.isProportional

Topic: fair_division   Node: 03964adfc099

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.isProportional`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/Checker.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Noncomputable proportionality Boolean reflection helper for `n` agents. Returns `true` iff every agent's bundle value is ≥ 1/n of the total. The value codomain is fixed to `ℝ`, so this is noncomputable.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N G : Type*} in
/-- Noncomputable proportionality Boolean reflection helper for `n` agents. Returns `true` iff every agent's bundle value is ≥ 1/n of the total. The value codomain is fixed to `ℝ`, so this is noncomputable. -/
noncomputable def SocialChoice.FairDivision.Indivisible.isProportional [Fintype N] (n : ℕ)
    (v : Valuation N G) (allGoods : Finset G) (A : Allocation N G) : Bool :=
  decide (∀ i : N, v.val i allGoods ≤ (n : ℝ) * v.val i (A i))

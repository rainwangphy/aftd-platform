import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleIsEFXOfSingletonBundle
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleIsEFX

/-!
# SocialChoice.FairDivision.Indivisible.efx_two_agents_two_goods

Topic: fair_division   Node: b971fb33bd91

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.efx_two_agents_two_goods`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/EFX.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**EFX for 2 agents and 2 goods**: the allocation giving one good to each agent is EFX. For any two goods `g₀` and `g₁`, the allocation `A 0 = {g₀}`, `A 1 = {g₁}` satisfies EFX for both agents, provided each agent values the empty bundle at most their own good. This holds for any additive nonneg valuation (`v.val i ∅ = 0 ≤ v.val i {g}`). *Proof*: Each bundle is a singleton. Removing the one element leaves `∅`, so the EFX condition reduces to `v.val j ∅ ≤ v.val j (A j)`, which holds by hypothesis.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N G : Type*} in
/-- **EFX for 2 agents and 2 goods**: the allocation giving one good to each agent is EFX. For any two goods `g₀` and `g₁`, the allocation `A 0 = {g₀}`, `A 1 = {g₁}` satisfies EFX for both agents, provided each agent values the empty bundle at most their own good. This holds for any additive nonneg valuation (`v.val i ∅ = 0 ≤ v.val i {g}`). *Proof*: Each bundle is a singleton. Removing the one element leaves `∅`, so the EFX condition reduces to `v.val j ∅ ≤ v.val j (A j)`, which holds by hypothesis. -/
theorem SocialChoice.FairDivision.Indivisible.efx_two_agents_two_goods [DecidableEq G]
    (v : Valuation (Fin 2) G) {g₀ g₁ : G}
    (h₀ : v.val 0 ∅ ≤ v.val 0 {g₀})
    (h₁ : v.val 1 ∅ ≤ v.val 1 {g₁})
    (A : Allocation (Fin 2) G) (hA0 : A 0 = {g₀}) (hA1 : A 1 = {g₁}) :
    IsEFX v A := by
  intro i j hij h hh
  fin_cases i
  · -- i = 0
    fin_cases j
    · exact absurd rfl hij              -- j = 0: contradiction
    · -- j = 1: agent 0 EFX w.r.t. agent 1; A 1 = {g₁} is singleton
      apply isEFX_of_singleton_bundle v A 1 0 hA1 _ h hh
      rw [hA0]; exact h₀
  · -- i = 1
    fin_cases j
    · -- j = 0: agent 1 EFX w.r.t. agent 0; A 0 = {g₀} is singleton
      apply isEFX_of_singleton_bundle v A 0 1 hA0 _ h hh
      rw [hA1]; exact h₁
    · exact absurd rfl hij              -- j = 1: contradiction

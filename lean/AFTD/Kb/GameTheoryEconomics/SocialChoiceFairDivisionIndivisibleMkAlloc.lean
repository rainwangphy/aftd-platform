import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAllocation

/-!
# SocialChoice.FairDivision.Indivisible.mkAlloc

Topic: fair_division   Node: c87a8e1de347

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.mkAlloc`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/EFX.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**EFX existence for 2 agents** (general m goods, additive nonneg valuations). For any set of goods and additive nonneg valuation, a complete EFX allocation exists. The proof uses the maximality argument outlined in the module header. The key cases are: - Agent 0 EFX follows trivially from the maximality construction. - Agent 1 EFX follows by contradiction: a swap or move argument improves agent 1's value while preserving agent 0's non-envy, contradicting maximality. The residual case (Case C: the best-good argument for zero-v₁ goods) is handled by the minimization over `S_star.card`, which rules out keeping the same agent-1 value with a strictly smaller chosen bundle.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N G : Type*} in
/-- **EFX existence for 2 agents** (general m goods, additive nonneg valuations). For any set of goods and additive nonneg valuation, a complete EFX allocation exists. The proof uses the maximality argument outlined in the module header. The key cases are: - Agent 0 EFX follows trivially from the maximality construction. - Agent 1 EFX follows by contradiction: a swap or move argument improves agent 1's value while preserving agent 0's non-envy, contradicting maximality. The residual case (Case C: the best-good argument for zero-v₁ goods) is handled by the minimization over `S_star.card`, which rules out keeping the same agent-1 value with a strictly smaller chosen bundle. -/
noncomputable def SocialChoice.FairDivision.Indivisible.mkAlloc [DecidableEq G] (allGoods S : Finset G) :
    Allocation (Fin 2) G :=
  fun i => if i = 0 then S else allGoods \ S

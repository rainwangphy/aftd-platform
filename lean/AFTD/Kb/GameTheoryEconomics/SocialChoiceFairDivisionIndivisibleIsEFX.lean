import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAllocation
import AFTD.Kb.Tcs.G

/-!
# SocialChoice.FairDivision.Indivisible.IsEFX

Topic: fair_division   Node: ace37dc1f32b

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.IsEFX`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/Fairness.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Envy-free up to any good (EFX): for any envied bundle, removing *any* item from it eliminates the envy. `∀ i ≠ j, ∀ g ∈ A_j, v_i(A_j \ {g}) ≤ v_i(A_i)`. Strictly stronger than EF1 (any witness vs. some witness). EFX exists for n = 2 (trivial) and n = 3 (Chaudhury-Garg-Mehlhorn 2020). Existence for n ≥ 4 is the major open problem in fair division. [AGT Ch.11; EC 2020 arXiv:2005.06878]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N G : Type*} in
/-- Envy-free up to any good (EFX): for any envied bundle, removing *any* item from it eliminates the envy. `∀ i ≠ j, ∀ g ∈ A_j, v_i(A_j \ {g}) ≤ v_i(A_i)`. Strictly stronger than EF1 (any witness vs. some witness). EFX exists for n = 2 (trivial) and n = 3 (Chaudhury-Garg-Mehlhorn 2020). Existence for n ≥ 4 is the major open problem in fair division. [AGT Ch.11; EC 2020 arXiv:2005.06878] -/
def SocialChoice.FairDivision.Indivisible.IsEFX [DecidableEq G] (v : Valuation N G) (A : Allocation N G) : Prop :=
  ∀ i j : N, i ≠ j →
    ∀ g ∈ A j, v.val i (A j \ {g}) ≤ v.val i (A i)

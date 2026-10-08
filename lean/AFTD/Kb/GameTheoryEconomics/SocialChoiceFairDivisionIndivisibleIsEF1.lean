import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAllocation
import AFTD.Kb.Tcs.G

/-!
# SocialChoice.FairDivision.Indivisible.IsEF1

Topic: fair_division   Node: 5ee033628d68

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.IsEF1`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/Fairness.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Envy-free up to one good (EF1): for any envied bundle, removing *some* item from it eliminates the envy. `∀ i ≠ j, A_j nonempty → ∃ g ∈ A_j, v_i(A_j \ {g}) ≤ v_i(A_i)`. The `Nonempty` guard is needed because the existential is vacuous for `A j = ∅` (an agent cannot envy an empty bundle). EF1 always exists; see `RoundRobin.lean`. [AGT Ch.11; Lipton et al. 2004]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N G : Type*} in
/-- Envy-free up to one good (EF1): for any envied bundle, removing *some* item from it eliminates the envy. `∀ i ≠ j, A_j nonempty → ∃ g ∈ A_j, v_i(A_j \ {g}) ≤ v_i(A_i)`. The `Nonempty` guard is needed because the existential is vacuous for `A j = ∅` (an agent cannot envy an empty bundle). EF1 always exists; see `RoundRobin.lean`. [AGT Ch.11; Lipton et al. 2004] -/
def SocialChoice.FairDivision.Indivisible.IsEF1 [DecidableEq G] (v : Valuation N G) (A : Allocation N G) : Prop :=
  ∀ i j : N, i ≠ j → (A j).Nonempty →
    ∃ g ∈ A j, v.val i (A j \ {g}) ≤ v.val i (A i)

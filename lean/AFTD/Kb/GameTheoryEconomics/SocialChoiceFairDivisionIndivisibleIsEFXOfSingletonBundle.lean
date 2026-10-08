import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation

/-!
# SocialChoice.FairDivision.Indivisible.isEFX_of_singleton_bundle

Topic: fair_division   Node: 8f416a02b603

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.isEFX_of_singleton_bundle`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/EFX.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If agent `i`'s bundle is a singleton `{g}`, then agent `j` is EFX with respect to agent `i`: removing the sole good from `A i` leaves `∅`, which agent `j` values at most their own bundle. The hypothesis `h_empty_le : v.val j ∅ ≤ v.val j (A j)` is satisfied whenever valuations are additive with nonneg weights (`AdditiveValuation` with `0 ≤ w.weight j g` for all `g`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N G : Type*} in
/-- If agent `i`'s bundle is a singleton `{g}`, then agent `j` is EFX with respect to agent `i`: removing the sole good from `A i` leaves `∅`, which agent `j` values at most their own bundle. The hypothesis `h_empty_le : v.val j ∅ ≤ v.val j (A j)` is satisfied whenever valuations are additive with nonneg weights (`AdditiveValuation` with `0 ≤ w.weight j g` for all `g`). -/
lemma SocialChoice.FairDivision.Indivisible.isEFX_of_singleton_bundle [DecidableEq G]
    (v : Valuation (Fin 2) G) (A : Allocation (Fin 2) G)
    (i j : Fin 2) {g : G}
    (hAi : A i = {g})
    (h_empty_le : v.val j ∅ ≤ v.val j (A j)) :
    ∀ h ∈ A i, v.val j (A i \ {h}) ≤ v.val j (A j) := by
  intro h hh
  have heq : h = g := by rwa [hAi, mem_singleton] at hh
  have hempty : A i \ {h} = ∅ := by simp [hAi, heq]
  rw [hempty]
  exact h_empty_le

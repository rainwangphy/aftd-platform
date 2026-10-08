import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleIsAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleMkAlloc

/-!
# SocialChoice.FairDivision.Indivisible.mkAlloc_isAllocation

Topic: fair_division   Node: 61242e141ac3

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.mkAlloc_isAllocation`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/EFX.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.FairDivision.Indivisible.mkAlloc_isAllocation
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N G : Type*} in
lemma SocialChoice.FairDivision.Indivisible.mkAlloc_isAllocation [DecidableEq G] (allGoods S : Finset G)
    (hS : S ⊆ allGoods) : IsAllocation allGoods (mkAlloc allGoods S) := by
  constructor <;> simp_all +decide [ Finset.ext_iff ];
  · exact ⟨ Finset.disjoint_sdiff, Finset.disjoint_sdiff.symm ⟩;
  · intro g; unfold mkAlloc; by_cases hg : g ∈ S <;> aesop;

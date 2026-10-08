import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleIsAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleMmsValue

/-!
# SocialChoice.FairDivision.Indivisible.mmsValue_nonneg

Topic: fair_division   Node: 24e0da06ae83

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.mmsValue_nonneg`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/MMS.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For nonneg valuations with at least one complete allocation, the MMS value is nonneg. `hne` ensures the `iSup` is nonempty. `[Fintype G]` makes the allocation subtype `[Finite]`, enabling `Finite.le_ciSup` without a separate `BddAbove` hypothesis.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N G : Type*} in
variable [Fintype N] [DecidableEq G] in
/-- For nonneg valuations with at least one complete allocation, the MMS value is nonneg. `hne` ensures the `iSup` is nonempty. `[Fintype G]` makes the allocation subtype `[Finite]`, enabling `Finite.le_ciSup` without a separate `BddAbove` hypothesis. -/
lemma SocialChoice.FairDivision.Indivisible.mmsValue_nonneg [Fintype G]
    (v : Valuation N G) (allGoods : Finset G) (i : N)
    (hne : Nonempty {A : Allocation N G // IsAllocation allGoods A})
    (hnonneg : ∀ S : Finset G, 0 ≤ v.val i S) :
    0 ≤ mmsValue v allGoods i := by
  haveI : Nonempty N := ⟨i⟩
  haveI : Fintype (Finset G) := Finset.fintype
  haveI : DecidableEq N := Classical.typeDecidableEq N
  haveI : Fintype (Allocation N G) :=
    @Pi.instFintype N (fun _ => Finset G) _ _ (fun _ => inferInstance)
  haveI : DecidablePred (fun A' : Allocation N G => IsAllocation allGoods A') :=
    Classical.decPred _
  haveI : Finite {A : Allocation N G // IsAllocation allGoods A} := inferInstance
  obtain ⟨⟨B, hB⟩⟩ := hne
  calc 0 ≤ iInf (fun j : N => v.val i (B j)) :=
        le_ciInf (fun j => hnonneg (B j))
    _ ≤ mmsValue v allGoods i :=
        Finite.le_ciSup (fun B' : {A : Allocation N G // IsAllocation allGoods A} =>
          iInf fun j : N => v.val i (B'.val j)) ⟨B, hB⟩

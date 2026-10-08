import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleIsAllocation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleIsMaxminShare
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleIsAlphaMMS
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleMmsValue

/-!
# SocialChoice.FairDivision.Indivisible.isMaxminShare_iff_isAlphaMMS_one

Topic: fair_division   Node: 58643e489d85

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.Indivisible.isMaxminShare_iff_isAlphaMMS_one`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Indivisible/MMS.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`IsMaxminShare` from `Fairness.lean` coincides with `IsAlphaMMS 1`. **→ direction** (`IsMaxminShare → IsAlphaMMS 1`): for every complete `B`, there exists `j` with `v_i(B_j) ≤ v_i(A_i)`, so `iInf_j v_i(B_j) ≤ v_i(A_i)`. Then `ciSup_le` gives `mmsValue ≤ v_i(A_i)`, and `1 * mmsValue = mmsValue` by `one_mul`. **← direction** (`IsAlphaMMS 1 → IsMaxminShare`): for any complete `B`, `iInf_j v_i(B_j) ≤ mmsValue ≤ v_i(A_i)`. Since `N` is `Nonempty` and `Fintype`, the infimum is achieved at some `j*`, giving `v_i(B_{j*}) ≤ v_i(A_i)`. `[Nonempty N]` ensures `iInf` is nonempty. `[Fintype G]` makes the allocation subtype `[Finite]`, enabling `Finite.le_ciSup` in the ← direction. `hne` is required by the → direction (to call `ciSup_le`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N G : Type*} in
variable [Fintype N] [DecidableEq G] in
/-- `IsMaxminShare` from `Fairness.lean` coincides with `IsAlphaMMS 1`. **→ direction** (`IsMaxminShare → IsAlphaMMS 1`): for every complete `B`, there exists `j` with `v_i(B_j) ≤ v_i(A_i)`, so `iInf_j v_i(B_j) ≤ v_i(A_i)`. Then `ciSup_le` gives `mmsValue ≤ v_i(A_i)`, and `1 * mmsValue = mmsValue` by `one_mul`. **← direction** (`IsAlphaMMS 1 → IsMaxminShare`): for any complete `B`, `iInf_j v_i(B_j) ≤ mmsValue ≤ v_i(A_i)`. Since `N` is `Nonempty` and `Fintype`, the infimum is achieved at some `j*`, giving `v_i(B_{j*}) ≤ v_i(A_i)`. `[Nonempty N]` ensures `iInf` is nonempty. `[Fintype G]` makes the allocation subtype `[Finite]`, enabling `Finite.le_ciSup` in the ← direction. `hne` is required by the → direction (to call `ciSup_le`). -/
theorem SocialChoice.FairDivision.Indivisible.isMaxminShare_iff_isAlphaMMS_one
    [Nonempty N] [Fintype G]
    (v : Valuation N G) (allGoods : Finset G) (A : Allocation N G)
    (hne : Nonempty {A' : Allocation N G // IsAllocation allGoods A'}) :
    IsMaxminShare v allGoods A ↔ IsAlphaMMS 1 v allGoods A := by
  constructor
  · intro hmms
    simp only [IsAlphaMMS, one_mul]
    intro i
    haveI : Nonempty {A' : Allocation N G // IsAllocation allGoods A'} := hne
    apply ciSup_le
    intro ⟨B, hB⟩
    obtain ⟨j, hj⟩ := hmms i B hB
    exact le_trans (Finite.ciInf_le (fun j' => v.val i (B j')) j) hj
  · intro halpha i B hB
    simp only [IsAlphaMMS, one_mul] at halpha
    haveI : Fintype (Finset G) := Finset.fintype
    haveI : DecidableEq N := Classical.typeDecidableEq N
    haveI : Fintype (Allocation N G) :=
      @Pi.instFintype N (fun _ => Finset G) _ _ (fun _ => inferInstance)
    haveI : DecidablePred (fun A' : Allocation N G => IsAllocation allGoods A') :=
      Classical.decPred _
    haveI : Finite {A' : Allocation N G // IsAllocation allGoods A'} := inferInstance
    obtain ⟨j, _, hj_min⟩ := Finset.exists_min_image Finset.univ (fun j => v.val i (B j))
      ⟨Classical.choice ‹Nonempty N›, Finset.mem_univ _⟩
    refine ⟨j, ?_⟩
    by_contra h_neg
    push_neg at h_neg
    have h1 : iInf (fun j' : N => v.val i (B j')) = v.val i (B j) :=
      le_antisymm (Finite.ciInf_le _ j) (le_ciInf fun j' => hj_min j' (Finset.mem_univ _))
    have h2 : v.val i (A i) < iInf (fun j' : N => v.val i (B j')) := h1 ▸ h_neg
    have h3 : iInf (fun j' : N => v.val i (B j')) ≤ mmsValue v allGoods i :=
      Finite.le_ciSup (fun B' : {A' : Allocation N G // IsAllocation allGoods A'} =>
        iInf fun j' => v.val i (B'.val j')) ⟨B, hB⟩
    exact absurd (lt_of_lt_of_le h2 (le_trans h3 (halpha i))) (lt_irrefl _)

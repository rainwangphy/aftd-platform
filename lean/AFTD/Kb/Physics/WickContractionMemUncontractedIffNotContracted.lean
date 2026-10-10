import AFTD.Prelude
import AFTD.Kb.Physics.WickContraction
import AFTD.Kb.Physics.WickContractionUncontracted
import AFTD.Kb.Physics.WickContractionGetDual
import AFTD.Kb.Physics.FieldSpecification
import AFTD.Kb.Physics.WickContractionCongrRefl
import AFTD.Kb.Physics.WickContractionCardCongr
import AFTD.Kb.Physics.WickContractionCongrTrans
import AFTD.Kb.Physics.WickContractionCongrTransApply
import AFTD.Kb.Physics.WickContractionCongrLiftRfl
import AFTD.Kb.Physics.WickContractionGetDualOneEqNone
import AFTD.Kb.Physics.WickContractionGetDualGetSelfMem
import AFTD.Kb.Physics.WickContractionSelfGetDualGetMem
import AFTD.Kb.Physics.WickContractionSelfNeGetDualGet
import AFTD.Kb.Physics.WickContractionGetDualGetSelfNeq
import AFTD.Kb.Physics.WickContractionGetDualGetDualGetGet
import AFTD.Kb.Physics.WickContractionFstFieldOfContractCongr
import AFTD.Kb.Physics.WickContractionSndFieldOfContractCongr
import AFTD.Kb.Physics.WickContractionFstFieldOfContractMem
import AFTD.Kb.Physics.WickContractionFstFieldOfContractGetDual
import AFTD.Kb.Physics.WickContractionSndFieldOfContractMem
import AFTD.Kb.Physics.WickContractionSndFieldOfContractGetDual
import AFTD.Kb.Physics.WickContractionUncontractedCongrNone
import AFTD.Kb.Physics.WickContractionUncontractedCongrSome
import AFTD.Kb.Physics.WickContractionInstDecidableEq
import AFTD.Kb.GameTheoryEconomics.LxvCheckSpec
import AFTD.Kb.GameTheoryEconomics.CatchUpBestMapNeLossIff
import AFTD.Kb.GameTheoryEconomics.PermCardLeftGtLe
import AFTD.Kb.GameTheoryEconomics.CatchUpValueTripleWinOfSumLt
import AFTD.Kb.Tcs.CardPauliStringsExactSupport

/-!
# WickContraction.mem_uncontracted_iff_not_contracted

Topic: quantum_field_theory   Node: dec985fc0403

Provenance: formalization of a published result. Source: Physlib, `WickContraction.mem_uncontracted_iff_not_contracted`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/WickContraction/Uncontracted.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

WickContraction.mem_uncontracted_iff_not_contracted
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open WickContraction in
variable {𝓕 : FieldSpecification} in
variable {n : ℕ} (c : WickContraction n) in
set_option backward.isDefEq.respectTransparency false in
lemma WickContraction.mem_uncontracted_iff_not_contracted (i : Fin n) :
    i ∈ c.uncontracted ↔ ∀ p ∈ c.1, i ∉ p := by
  simp only [uncontracted, getDual?, Finset.mem_filter, Finset.mem_univ, true_and]
  apply Iff.intro
  · intro h p hp
    have hp := c.2.1 p hp
    rw [Finset.card_eq_two] at hp
    obtain ⟨a, b, ha, hb, hab⟩ := hp
    rw [Fin.find?_eq_none_iff] at h
    by_contra hn
    simp only [Finset.mem_insert, Finset.mem_singleton] at hn
    rcases hn with hn | hn
    · subst hn
      simp at h
      exact h b hp
    · subst hn
      rw [Finset.pair_comm] at hp
      simp at h
      exact h a hp
  · intro h
    rw [Fin.find?_eq_none_iff]
    by_contra hn
    simp only [decide_eq_false_iff_not, not_forall, Decidable.not_not] at hn
    obtain ⟨j, hj⟩ := hn
    apply h {i, j} hj
    simp

import AFTD.Prelude
import AFTD.Kb.Physics.WickContraction
import AFTD.Kb.Physics.WickContractionUncontracted
import AFTD.Kb.Physics.WickContractionErase
import AFTD.Kb.Physics.WickContractionGetDual
import AFTD.Kb.Physics.WickContractionGetDualEqSomeIffMem
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
import AFTD.Kb.Physics.WickContractionGetDualEmptyEqNone
import AFTD.Kb.Physics.WickContractionUncontractedEmpty
import AFTD.Kb.Physics.WickContractionInstDecidableEq
import AFTD.Kb.GameTheoryEconomics.PermCardLeftGtLe
import AFTD.Kb.GameTheoryEconomics.CatchUpValueTripleWinOfSumLt
import AFTD.Kb.GameTheoryEconomics.MxsFairImpProp1FairOfSubmodular

/-!
# WickContraction.mem_erase_uncontracted_iff

Topic: quantum_field_theory   Node: 793f7b8c9239

Provenance: formalization of a published result. Source: Physlib, `WickContraction.mem_erase_uncontracted_iff`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/WickContraction/Erase.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

WickContraction.mem_erase_uncontracted_iff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open WickContraction in
variable {𝓕 : FieldSpecification} in
variable {n : ℕ} (c : WickContraction n) in
set_option backward.isDefEq.respectTransparency false in
lemma WickContraction.mem_erase_uncontracted_iff (c : WickContraction n.succ) (i : Fin n.succ) (j : Fin n) :
    j ∈ (c.erase i).uncontracted ↔
    i.succAbove j ∈ c.uncontracted ∨ c.getDual? (i.succAbove j) = some i := by
  rw [getDual?_eq_some_iff_mem]
  simp only [uncontracted, getDual?, erase, Nat.succ_eq_add_one, Finset.mem_filter, Finset.mem_univ,
    Finset.map_insert, Fin.succAboveEmb_apply, Finset.map_singleton, true_and]
  rw [Fin.find?_eq_none_iff, Fin.find?_eq_none_iff]
  apply Iff.intro
  · intro h
    by_cases hi : {i.succAbove j, i} ∈ c.1
    · simp [hi]
    · apply Or.inl
      intro k
      by_cases hi' : k = i
      · subst hi'
        simpa using hi
      · simp only [← Fin.exists_succAbove_eq_iff] at hi'
        obtain ⟨z, hz⟩ := hi'
        subst hz
        exact h z
  · intro h k
    rcases h with h | h
    · exact h (i.succAbove k)
    · by_contra hn
      have hc := c.2.2 _ h _ (by simpa using hn)
      simp only [Nat.succ_eq_add_one, Finset.disjoint_insert_right, Finset.mem_insert,
        Finset.mem_singleton, true_or, not_true_eq_false, Finset.disjoint_singleton_right, not_or,
        false_and, or_false] at hc
      have hi : i ∈ ({i.succAbove j, i.succAbove k} : Finset (Fin n.succ)) := by
        simp [← hc]
      simp only [Nat.succ_eq_add_one, Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with hi | hi
      · exact False.elim (Fin.succAbove_ne _ _ hi.symm)
      · exact False.elim (Fin.succAbove_ne _ _ hi.symm)

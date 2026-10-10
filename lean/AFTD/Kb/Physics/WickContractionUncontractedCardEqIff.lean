import AFTD.Prelude
import AFTD.Kb.Physics.WickContraction
import AFTD.Kb.Physics.WickContractionUncontracted
import AFTD.Kb.Physics.WickContractionEmpty
import AFTD.Kb.Physics.WickContractionInstDecidableEq
import AFTD.Kb.Physics.WickContractionExistsPairOfNotEqEmpty
import AFTD.Kb.Physics.WickContractionGetDual
import AFTD.Kb.Physics.WickContractionGetDualEqSomeIffMem
import AFTD.Kb.Physics.WickContractionUncontractedEmpty
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

/-!
# WickContraction.uncontracted_card_eq_iff

Topic: quantum_field_theory   Node: e0bd9a3b2d54

Provenance: formalization of a published result. Source: Physlib, `WickContraction.uncontracted_card_eq_iff`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/WickContraction/Uncontracted.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

WickContraction.uncontracted_card_eq_iff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open WickContraction in
variable {𝓕 : FieldSpecification} in
variable {n : ℕ} (c : WickContraction n) in
lemma WickContraction.uncontracted_card_eq_iff (c : WickContraction n) :
    c.uncontracted.card = n ↔ c = empty := by
  apply Iff.intro
  · intro h
    have hc : c.uncontracted.card = (Finset.univ (α := Fin n)).card := by simpa using h
    simp only [uncontracted] at hc
    rw [Finset.card_filter_eq_iff] at hc
    by_contra hn
    have hc' := exists_pair_of_not_eq_empty c hn
    obtain ⟨i, j, hij⟩ := hc'
    have hci : c.getDual? i = some j := by
      rw [@getDual?_eq_some_iff_mem]
      exact hij
    simp_all
  · intro h
    subst h
    simp

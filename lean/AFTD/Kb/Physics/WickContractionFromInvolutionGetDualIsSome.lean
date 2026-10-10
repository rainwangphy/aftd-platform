import AFTD.Prelude
import AFTD.Kb.Physics.WickContractionGetDual
import AFTD.Kb.Physics.WickContractionFromInvolution
import AFTD.Kb.Physics.WickContractionGetDualIsSomeIff
import AFTD.Kb.Physics.FieldSpecification
import AFTD.Kb.Physics.WickContraction
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
import AFTD.Kb.Physics.WickContractionInstDecidableEq
import AFTD.Kb.GameTheoryEconomics.PermCardLeftGtLe
import AFTD.Kb.GameTheoryEconomics.CatchUpValueTripleWinOfSumLt

/-!
# WickContraction.fromInvolution_getDual?_isSome

Topic: quantum_field_theory   Node: 84eb46a8a5ae

Provenance: formalization of a published result. Source: Physlib, `WickContraction.fromInvolution_getDual?_isSome`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/WickContraction/Involutions.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

WickContraction.fromInvolution_getDual?_isSome
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open WickContraction in
variable {𝓕 : FieldSpecification} in
variable {n : ℕ} (c : WickContraction n) in
@[simp]
lemma WickContraction.fromInvolution_getDual?_isSome (f : {f : Fin n → Fin n // Function.Involutive f})
    (i : Fin n) : ((fromInvolution f).getDual? i).isSome ↔ f.1 i ≠ i := by
  rw [getDual?_isSome_iff]
  apply Iff.intro
  · intro h
    obtain ⟨a, ha⟩ := h
    have ha2 := a.2
    simp only [fromInvolution, Finset.mem_filter, Finset.mem_univ, true_and] at ha2
    obtain ⟨j, h⟩ := ha2.2
    rw [← h] at ha
    have hj : f.1 j ≠ j := by
      intro hn
      rw [hn] at h
      simp [← h] at ha2
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact hj
    · rw [f.2]
      exact hj.symm
  · intro hi
    use ⟨{i, f.1 i}, by
      simp only [fromInvolution, Finset.mem_filter, Finset.mem_univ, exists_apply_eq_apply,
        and_true, true_and]
      exact Finset.card_pair hi.symm⟩
    simp

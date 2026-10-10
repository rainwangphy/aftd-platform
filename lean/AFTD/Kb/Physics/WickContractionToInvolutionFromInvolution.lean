import AFTD.Prelude
import AFTD.Kb.Physics.WickContraction
import AFTD.Kb.Physics.WickContractionFromInvolution
import AFTD.Kb.Physics.WickContractionToInvolution
import AFTD.Kb.Physics.WickContractionGetDual
import AFTD.Kb.Physics.WickContractionSelfGetDualGetMem
import AFTD.Kb.Physics.WickContractionFstFieldOfContract
import AFTD.Kb.Physics.WickContractionSndFieldOfContract
import AFTD.Kb.Physics.WickContractionFstFieldOfContractGetDual
import AFTD.Kb.Physics.WickContractionFinsetEqFstFieldOfContractSndFieldOfContract
import AFTD.Kb.Physics.FieldSpecification
import AFTD.Kb.Physics.WickContractionCongrRefl
import AFTD.Kb.Physics.WickContractionCardCongr
import AFTD.Kb.Physics.WickContractionCongrTrans
import AFTD.Kb.Physics.WickContractionCongrTransApply
import AFTD.Kb.Physics.WickContractionCongrLiftRfl
import AFTD.Kb.Physics.WickContractionGetDualOneEqNone
import AFTD.Kb.Physics.WickContractionGetDualGetSelfMem
import AFTD.Kb.Physics.WickContractionSelfNeGetDualGet
import AFTD.Kb.Physics.WickContractionGetDualGetSelfNeq
import AFTD.Kb.Physics.WickContractionGetDualGetDualGetGet
import AFTD.Kb.Physics.WickContractionFstFieldOfContractCongr
import AFTD.Kb.Physics.WickContractionSndFieldOfContractCongr
import AFTD.Kb.Physics.WickContractionFstFieldOfContractMem
import AFTD.Kb.Physics.WickContractionSndFieldOfContractMem
import AFTD.Kb.Physics.WickContractionSndFieldOfContractGetDual
import AFTD.Kb.Physics.WickContractionFromInvolutionGetDualIsSome
import AFTD.Kb.Physics.WickContractionFromInvolutionGetDualGet
import AFTD.Kb.Physics.WickContractionInstDecidableEq
import AFTD.Kb.GameTheoryEconomics.PermCardLeftGtLe

/-!
# WickContraction.toInvolution_fromInvolution

Topic: quantum_field_theory   Node: 127baeb65abd

Provenance: formalization of a published result. Source: Physlib, `WickContraction.toInvolution_fromInvolution`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/WickContraction/Involutions.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

WickContraction.toInvolution_fromInvolution
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open WickContraction in
variable {𝓕 : FieldSpecification} in
variable {n : ℕ} (c : WickContraction n) in
set_option backward.isDefEq.respectTransparency false in
lemma WickContraction.toInvolution_fromInvolution : fromInvolution c.toInvolution = c := by
  apply Subtype.ext
  simp only [fromInvolution, toInvolution]
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  apply Iff.intro
  · intro h
    obtain ⟨i, hi⟩ := h.2
    split at hi
    · subst hi
      simp
    · subst hi
      simp [Finset.insert_eq_of_mem] at h
  · intro ha
    refine ⟨c.2.1 a ha, c.fstFieldOfContract ⟨a, ha⟩, ?_⟩
    simp only [fstFieldOfContract_getDual?, Option.isSome_some, ↓reduceDIte, Option.get_some]
    exact (finset_eq_fstFieldOfContract_sndFieldOfContract c ⟨a, ha⟩).symm

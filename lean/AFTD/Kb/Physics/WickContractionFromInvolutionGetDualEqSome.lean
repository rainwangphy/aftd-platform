import AFTD.Prelude
import AFTD.Kb.Physics.WickContractionGetDual
import AFTD.Kb.Physics.WickContractionFromInvolution
import AFTD.Kb.Physics.WickContractionGetDualEqSomeIffMem
import AFTD.Kb.Physics.WickContractionFromInvolutionGetDualIsSome
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

/-!
# WickContraction.fromInvolution_getDual?_eq_some

Topic: quantum_field_theory   Node: 930c3a916b5b

Provenance: formalization of a published result. Source: Physlib, `WickContraction.fromInvolution_getDual?_eq_some`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/WickContraction/Involutions.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

WickContraction.fromInvolution_getDual?_eq_some
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open WickContraction in
variable {𝓕 : FieldSpecification} in
variable {n : ℕ} (c : WickContraction n) in
lemma WickContraction.fromInvolution_getDual?_eq_some (f : {f : Fin n → Fin n // Function.Involutive f}) (i : Fin n)
    (h : ((fromInvolution f).getDual? i).isSome) :
    ((fromInvolution f).getDual? i) = some (f.1 i) := by
  rw [getDual?_eq_some_iff_mem]
  simp only [fromInvolution, Finset.mem_filter, Finset.mem_univ, exists_apply_eq_apply, and_true,
    true_and]
  exact Finset.card_pair (Ne.symm ((fromInvolution_getDual?_isSome f i).mp h))

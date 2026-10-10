import AFTD.Prelude
import AFTD.Kb.Physics.WickContraction
import AFTD.Kb.Physics.WickContractionGetDual
import AFTD.Kb.Physics.WickContractionFstFieldOfContract
import AFTD.Kb.Physics.WickContractionSndFieldOfContract
import AFTD.Kb.Physics.FieldSpecification
import AFTD.Kb.Physics.WickContractionFinsetEqFstFieldOfContractSndFieldOfContract
import AFTD.Kb.Physics.WickContractionGetDualEqSomeIffMem
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
import AFTD.Kb.Physics.WickContractionInstDecidableEq

/-!
# WickContraction.fstFieldOfContract_getDual?

Topic: quantum_field_theory   Node: cb101379e8ab

Provenance: formalization of a published result. Source: Physlib, `WickContraction.fstFieldOfContract_getDual?`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/WickContraction/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

WickContraction.fstFieldOfContract_getDual?
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open WickContraction in
variable {𝓕 : FieldSpecification} in
variable {n : ℕ} (c : WickContraction n) in
@[simp]
lemma WickContraction.fstFieldOfContract_getDual? (c : WickContraction n) (a : c.1) :
    c.getDual? (c.fstFieldOfContract a) = some (c.sndFieldOfContract a) := by
  simp [getDual?_eq_some_iff_mem, ← finset_eq_fstFieldOfContract_sndFieldOfContract]

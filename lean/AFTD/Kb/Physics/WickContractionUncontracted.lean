import AFTD.Prelude
import AFTD.Kb.Physics.WickContraction
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
import AFTD.Kb.Physics.WickContractionInstDecidableEq

/-!
# WickContraction.uncontracted

Topic: quantum_field_theory   Node: 591749786f8d

Provenance: formalization of a published result. Source: Physlib, `WickContraction.uncontracted`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/WickContraction/Uncontracted.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For a Wick contraction `c`, `c.uncontracted` is defined as the finset of elements of `Fin n` which are not in any contracted pair.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open WickContraction in
variable {𝓕 : FieldSpecification} in
variable {n : ℕ} (c : WickContraction n) in
/-- For a Wick contraction `c`, `c.uncontracted` is defined as the finset of elements of `Fin n` which are not in any contracted pair. -/
def WickContraction.uncontracted : Finset (Fin n) := Finset.filter (fun i => c.getDual? i = none) (Finset.univ)

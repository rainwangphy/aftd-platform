import AFTD.Prelude
import AFTD.Kb.Physics.WickContraction
import AFTD.Kb.Physics.WickContractionToInvolution
import AFTD.Kb.Physics.WickContractionFromInvolution
import AFTD.Kb.Physics.WickContractionToInvolutionFromInvolution
import AFTD.Kb.Physics.WickContractionFromInvolutionToInvolution
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
import AFTD.Kb.Physics.WickContractionFromInvolutionGetDualIsSome
import AFTD.Kb.Physics.WickContractionFromInvolutionGetDualGet
import AFTD.Kb.Physics.WickContractionInstDecidableEq

/-!
# WickContraction.equivInvolution

Topic: quantum_field_theory   Node: 751236f0b057

Provenance: formalization of a published result. Source: Physlib, `WickContraction.equivInvolution`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/WickContraction/Involutions.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The equivalence between Wick contractions for `n` and involutions of `Fin n`. The involution of `Fin n` associated with a Wick contraction `c : WickContraction n` as follows. If `i : Fin n` is contracted in `c` then it is taken to its dual, otherwise it is taken to itself.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open WickContraction in
variable {𝓕 : FieldSpecification} in
variable {n : ℕ} (c : WickContraction n) in
/-- The equivalence between Wick contractions for `n` and involutions of `Fin n`. The involution of `Fin n` associated with a Wick contraction `c : WickContraction n` as follows. If `i : Fin n` is contracted in `c` then it is taken to its dual, otherwise it is taken to itself. -/
def WickContraction.equivInvolution : WickContraction n ≃ {f : Fin n → Fin n // Function.Involutive f} where
  toFun := toInvolution
  invFun := fromInvolution
  left_inv := toInvolution_fromInvolution
  right_inv := fromInvolution_toInvolution

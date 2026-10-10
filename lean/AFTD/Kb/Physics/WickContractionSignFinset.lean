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
# WickContraction.signFinset

Topic: quantum_field_theory   Node: a1e4f0a8d825

Provenance: formalization of a published result. Source: Physlib, `WickContraction.signFinset`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/WickContraction/Sign/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a Wick contraction `c : WickContraction n` and `i1 i2 : Fin n` the finite set of elements of `Fin n` between `i1` and `i2` which are either uncontracted or are contracted but are contracted with an element occurring after `i1`. In other words, the elements of `Fin n` between `i1` and `i2` which are not contracted with before `i1`. One should assume `i1 < i2` otherwise this finite set is empty.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open WickContraction in
variable {𝓕 : FieldSpecification} in
variable {n : ℕ} (c : WickContraction n) in
/-- Given a Wick contraction `c : WickContraction n` and `i1 i2 : Fin n` the finite set of elements of `Fin n` between `i1` and `i2` which are either uncontracted or are contracted but are contracted with an element occurring after `i1`. In other words, the elements of `Fin n` between `i1` and `i2` which are not contracted with before `i1`. One should assume `i1 < i2` otherwise this finite set is empty. -/
def WickContraction.signFinset (c : WickContraction n) (i1 i2 : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => i1 < i ∧ i < i2 ∧
  (c.getDual? i = none ∨ ∀ (h : (c.getDual? i).isSome), i1 < (c.getDual? i).get h))

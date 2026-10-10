import AFTD.Prelude
import AFTD.Kb.Physics.WickContraction
import AFTD.Kb.Physics.WickContractionGetDual
import AFTD.Kb.Physics.WickContractionGetDualIsSomeIff
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
import AFTD.Kb.Physics.WickContractionInstDecidableEq

/-!
# WickContraction.getDual?_isSome_of_mem

Topic: quantum_field_theory   Node: 42a79ae5bdd8

Provenance: formalization of a published result. Source: Physlib, `WickContraction.getDual?_isSome_of_mem`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/WickContraction/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

WickContraction.getDual?_isSome_of_mem
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open WickContraction in
variable {𝓕 : FieldSpecification} in
variable {n : ℕ} (c : WickContraction n) in
lemma WickContraction.getDual?_isSome_of_mem (a : c.1) (i : a.1) : (c.getDual? i).isSome :=
  (c.getDual?_isSome_iff i).mpr ⟨a, i.2⟩

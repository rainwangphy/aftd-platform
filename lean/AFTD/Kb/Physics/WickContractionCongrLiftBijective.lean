import AFTD.Prelude
import AFTD.Kb.Physics.WickContraction
import AFTD.Kb.Physics.WickContractionCongr
import AFTD.Kb.Physics.WickContractionCongrLift
import AFTD.Kb.Physics.WickContractionCongrLiftInjective
import AFTD.Kb.Physics.WickContractionCongrLiftSurjective
import AFTD.Kb.Physics.FieldSpecification
import AFTD.Kb.Physics.WickContractionCongrRefl
import AFTD.Kb.Physics.WickContractionCardCongr
import AFTD.Kb.Physics.WickContractionCongrTrans
import AFTD.Kb.Physics.WickContractionCongrTransApply
import AFTD.Kb.Physics.WickContractionCongrLiftRfl
import AFTD.Kb.Physics.WickContractionInstDecidableEq

/-!
# WickContraction.congrLift_bijective

Topic: quantum_field_theory   Node: 7930770cb77a

Provenance: formalization of a published result. Source: Physlib, `WickContraction.congrLift_bijective`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/WickContraction/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

WickContraction.congrLift_bijective
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open WickContraction in
variable {𝓕 : FieldSpecification} in
variable {n : ℕ} (c : WickContraction n) in
lemma WickContraction.congrLift_bijective {n m : ℕ} {c : WickContraction n} (h : n = m) :
    Function.Bijective (c.congrLift h) :=
  ⟨c.congrLift_injective h, c.congrLift_surjective h⟩

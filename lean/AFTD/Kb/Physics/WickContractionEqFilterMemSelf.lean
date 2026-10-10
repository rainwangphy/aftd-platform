import AFTD.Prelude
import AFTD.Kb.Physics.WickContraction
import AFTD.Kb.Physics.FieldSpecification
import AFTD.Kb.Physics.WickContractionCongrRefl
import AFTD.Kb.Physics.WickContractionCardCongr
import AFTD.Kb.Physics.WickContractionCongrTrans
import AFTD.Kb.Physics.WickContractionCongrTransApply
import AFTD.Kb.Physics.WickContractionCongrLiftRfl
import AFTD.Kb.Physics.WickContractionInstDecidableEq

/-!
# WickContraction.eq_filter_mem_self

Topic: quantum_field_theory   Node: 2b22ce01dcb3

Provenance: formalization of a published result. Source: Physlib, `WickContraction.eq_filter_mem_self`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/WickContraction/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

WickContraction.eq_filter_mem_self
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {𝓕 : FieldSpecification} in
variable {n : ℕ} (c : WickContraction n) in
lemma WickContraction.eq_filter_mem_self : c.1 = Finset.filter (fun x => x ∈ c.1) Finset.univ :=
  (Finset.filter_univ_mem c.1).symm

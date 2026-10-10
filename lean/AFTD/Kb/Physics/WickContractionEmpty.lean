import AFTD.Prelude
import AFTD.Kb.Physics.WickContraction
import AFTD.Kb.Physics.FieldSpecification
import AFTD.Kb.Physics.WickContractionInstDecidableEq

/-!
# WickContraction.empty

Topic: quantum_field_theory   Node: 98f826b50ace

Provenance: formalization of a published result. Source: Physlib, `WickContraction.empty`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/WickContraction/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The contraction consisting of no contracted pairs.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {𝓕 : FieldSpecification} in
variable {n : ℕ} (c : WickContraction n) in
/-- The contraction consisting of no contracted pairs. -/
def WickContraction.empty : WickContraction n := ⟨∅, by simp, by simp⟩

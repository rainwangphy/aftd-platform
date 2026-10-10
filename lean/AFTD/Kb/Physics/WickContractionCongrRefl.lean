import AFTD.Prelude
import AFTD.Kb.Physics.WickContraction
import AFTD.Kb.Physics.WickContractionCongr
import AFTD.Kb.Physics.FieldSpecification
import AFTD.Kb.Physics.WickContractionInstDecidableEq

/-!
# WickContraction.congr_refl

Topic: quantum_field_theory   Node: bd1a7e0d71a6

Provenance: formalization of a published result. Source: Physlib, `WickContraction.congr_refl`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/WickContraction/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

WickContraction.congr_refl
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open WickContraction in
variable {𝓕 : FieldSpecification} in
variable {n : ℕ} (c : WickContraction n) in
@[simp]
lemma WickContraction.congr_refl : c.congr rfl = c := rfl

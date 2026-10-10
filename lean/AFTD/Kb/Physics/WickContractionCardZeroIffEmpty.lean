import AFTD.Prelude
import AFTD.Kb.Physics.WickContraction
import AFTD.Kb.Physics.WickContractionEmpty
import AFTD.Kb.Physics.FieldSpecification
import AFTD.Kb.Physics.WickContractionInstDecidableEq

/-!
# WickContraction.card_zero_iff_empty

Topic: quantum_field_theory   Node: 04e0317e32ee

Provenance: formalization of a published result. Source: Physlib, `WickContraction.card_zero_iff_empty`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/WickContraction/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

WickContraction.card_zero_iff_empty
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open WickContraction in
variable {𝓕 : FieldSpecification} in
variable {n : ℕ} (c : WickContraction n) in
set_option backward.isDefEq.respectTransparency false in
lemma WickContraction.card_zero_iff_empty (c : WickContraction n) : c.1.card = 0 ↔ c = empty := by
  rw [Subtype.ext_iff, Finset.card_eq_zero, empty]

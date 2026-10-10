import AFTD.Prelude
import AFTD.Kb.Physics.WickContraction
import AFTD.Kb.Physics.WickContractionEmpty
import AFTD.Kb.Physics.FieldSpecification
import AFTD.Kb.Physics.WickContractionInstDecidableEq

/-!
# WickContraction.exists_pair_of_not_eq_empty

Topic: quantum_field_theory   Node: beb3337c0832

Provenance: formalization of a published result. Source: Physlib, `WickContraction.exists_pair_of_not_eq_empty`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/WickContraction/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

WickContraction.exists_pair_of_not_eq_empty
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open WickContraction in
variable {𝓕 : FieldSpecification} in
variable {n : ℕ} (c : WickContraction n) in
lemma WickContraction.exists_pair_of_not_eq_empty (c : WickContraction n) (h : c ≠ empty) :
    ∃ i j, {i, j} ∈ c.1 := by
  obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr fun hc => h (Subtype.ext hc)
  obtain ⟨i, j, -, rfl⟩ := Finset.card_eq_two.mp (c.2.1 a ha)
  exact ⟨i, j, ha⟩

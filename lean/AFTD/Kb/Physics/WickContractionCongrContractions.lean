import AFTD.Prelude
import AFTD.Kb.Physics.WickContraction
import AFTD.Kb.Physics.WickContractionCongr
import AFTD.Kb.Physics.FieldSpecification
import AFTD.Kb.Physics.WickContractionCongrRefl
import AFTD.Kb.Physics.WickContractionCardCongr
import AFTD.Kb.Physics.WickContractionInstDecidableEq
import AFTD.Kb.GameTheoryEconomics.PersuasionSliceCardFilter

/-!
# WickContraction.congr_contractions

Topic: quantum_field_theory   Node: 5e03588c2e2a

Provenance: formalization of a published result. Source: Physlib, `WickContraction.congr_contractions`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/WickContraction/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

WickContraction.congr_contractions
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open WickContraction in
variable {𝓕 : FieldSpecification} in
variable {n : ℕ} (c : WickContraction n) in
lemma WickContraction.congr_contractions {n m : ℕ} (h : n = m) (c : WickContraction n) :
    ((congr h) c).1 = Finset.map (Finset.mapEmbedding (finCongr h)).toEmbedding c.1 := by
  subst h
  ext a
  simp only [congr_refl, Finset.mem_map, RelEmbedding.coe_toEmbedding, finCongr_refl,
    Equiv.refl_toEmbedding]
  exact ⟨fun ha => ⟨a, ha, Finset.map_refl⟩,
    fun ⟨b, hb, hab⟩ => (Finset.map_refl.symm.trans hab) ▸ hb⟩

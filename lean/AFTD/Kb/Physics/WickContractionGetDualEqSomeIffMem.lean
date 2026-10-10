import AFTD.Prelude
import AFTD.Kb.Physics.WickContraction
import AFTD.Kb.Physics.WickContractionGetDual
import AFTD.Kb.Physics.FieldSpecification
import AFTD.Kb.Physics.WickContractionCongrRefl
import AFTD.Kb.Physics.WickContractionCardCongr
import AFTD.Kb.Physics.WickContractionCongrTrans
import AFTD.Kb.Physics.WickContractionCongrTransApply
import AFTD.Kb.Physics.WickContractionCongrLiftRfl
import AFTD.Kb.Physics.WickContractionInstDecidableEq
import AFTD.Kb.GameTheoryEconomics.LxvCheckSpec

/-!
# WickContraction.getDual?_eq_some_iff_mem

Topic: quantum_field_theory   Node: 0e28c60719d7

Provenance: formalization of a published result. Source: Physlib, `WickContraction.getDual?_eq_some_iff_mem`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/WickContraction/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

WickContraction.getDual?_eq_some_iff_mem
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open WickContraction in
variable {𝓕 : FieldSpecification} in
variable {n : ℕ} (c : WickContraction n) in
lemma WickContraction.getDual?_eq_some_iff_mem (i j : Fin n) :
    c.getDual? i = some j ↔ {i, j} ∈ c.1 := by
  rw [getDual?, Fin.find?_eq_some_iff]
  refine ⟨fun h => by simpa using h.1, fun h => ⟨by simpa using h, fun k hkj => ?_⟩⟩
  simp only [decide_eq_false_iff_not]
  intro hk
  rcases c.2.2 _ h _ hk with heq | hdisj
  · have hkm : k = i ∨ k = j := by simpa using (Finset.ext_iff.mp heq k).mpr (by simp)
    rcases hkm with rfl | rfl
    · simpa using c.2.1 _ hk
    · omega
  · simpa using Finset.disjoint_left.mp hdisj (Finset.mem_insert_self i {j})

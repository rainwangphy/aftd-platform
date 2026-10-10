import AFTD.Prelude
import AFTD.Kb.Physics.WickContraction
import AFTD.Kb.Physics.WickContractionGetDual
import AFTD.Kb.Physics.FieldSpecification
import AFTD.Kb.Physics.WickContractionGetDualEqSomeIffMem
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
import AFTD.Kb.GameTheoryEconomics.CatchUpValueTripleWinOfSumLt

/-!
# WickContraction.getDual?_isSome_iff

Topic: quantum_field_theory   Node: 00606653769e

Provenance: formalization of a published result. Source: Physlib, `WickContraction.getDual?_isSome_iff`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/WickContraction/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

WickContraction.getDual?_isSome_iff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open WickContraction in
variable {𝓕 : FieldSpecification} in
variable {n : ℕ} (c : WickContraction n) in
lemma WickContraction.getDual?_isSome_iff (i : Fin n) : (c.getDual? i).isSome ↔ ∃ (a : c.1), i ∈ a.1 := by
  simp only [Option.isSome_iff_exists, getDual?_eq_some_iff_mem]
  refine ⟨fun ⟨j, hj⟩ => ⟨⟨_, hj⟩, Finset.mem_insert_self ..⟩, fun ⟨a, ha⟩ => ?_⟩
  obtain ⟨x, y, -, hxy⟩ := Finset.card_eq_two.mp (c.2.1 a a.2)
  rw [hxy] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · exact ⟨y, hxy ▸ a.2⟩
  · rw [Finset.pair_comm] at hxy
    exact ⟨x, hxy ▸ a.2⟩

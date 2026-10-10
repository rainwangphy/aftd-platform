import AFTD.Prelude
import AFTD.Kb.Physics.WickContraction
import AFTD.Kb.Physics.WickContractionFstFieldOfContract
import AFTD.Kb.Physics.WickContractionSndFieldOfContract
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
import AFTD.Kb.Physics.WickContractionGetDualGetDualGetGet
import AFTD.Kb.Physics.WickContractionFstFieldOfContractCongr
import AFTD.Kb.Physics.WickContractionSndFieldOfContractCongr
import AFTD.Kb.Physics.WickContractionInstDecidableEq
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# WickContraction.finset_eq_fstFieldOfContract_sndFieldOfContract

Topic: quantum_field_theory   Node: a3b81357bdd6

Provenance: formalization of a published result. Source: Physlib, `WickContraction.finset_eq_fstFieldOfContract_sndFieldOfContract`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/WickContraction/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

WickContraction.finset_eq_fstFieldOfContract_sndFieldOfContract
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open WickContraction in
variable {𝓕 : FieldSpecification} in
variable {n : ℕ} (c : WickContraction n) in
lemma WickContraction.finset_eq_fstFieldOfContract_sndFieldOfContract (c : WickContraction n) (a : c.1) :
    a.1 = {c.fstFieldOfContract a, c.sndFieldOfContract a} := by
  suffices h : ∀ x y : Fin n, x < y → a.1 = {x, y} →
      a.1 = {c.fstFieldOfContract a, c.sndFieldOfContract a} by
    obtain ⟨x, y, hxy, ha⟩ := Finset.card_eq_two.mp (c.2.1 a.1 a.2)
    rcases lt_or_gt_of_ne hxy with h' | h'
    · exact h x y h' ha
    · exact h y x h' (ha.trans (Finset.pair_comm x y))
  intro x y hxy ha
  have h1 : ∀ b ∈ ({y} : Finset (Fin n)), x ≤ b := by simp [hxy.le]
  have hs : a.1.sort (· ≤ ·) = [x, y] := by
    rw [ha, Finset.sort_insert _ h1 (by simp [hxy.ne]), Finset.sort_singleton]
  rw [ha]
  simp [fstFieldOfContract, sndFieldOfContract, hs]

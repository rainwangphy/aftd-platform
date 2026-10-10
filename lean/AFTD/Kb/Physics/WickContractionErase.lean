import AFTD.Prelude
import AFTD.Kb.Physics.WickContraction
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
import AFTD.Kb.Physics.WickContractionFstFieldOfContractMem
import AFTD.Kb.Physics.WickContractionFstFieldOfContractGetDual
import AFTD.Kb.Physics.WickContractionSndFieldOfContractMem
import AFTD.Kb.Physics.WickContractionSndFieldOfContractGetDual
import AFTD.Kb.Physics.WickContractionUncontractedCongrNone
import AFTD.Kb.Physics.WickContractionUncontractedCongrSome
import AFTD.Kb.Physics.WickContractionGetDualEmptyEqNone
import AFTD.Kb.Physics.WickContractionUncontractedEmpty
import AFTD.Kb.Physics.WickContractionInstDecidableEq
import AFTD.Kb.GameTheoryEconomics.PermCardLeftGtLe

/-!
# WickContraction.erase

Topic: quantum_field_theory   Node: ef9b397adf30

Provenance: formalization of a published result. Source: Physlib, `WickContraction.erase`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/WickContraction/Erase.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a Wick contraction `WickContraction n.succ` and a `i : Fin n.succ` the Wick contraction associated with `n` obtained by removing `i`. If `i` is contracted with `j` in the new Wick contraction `j` will be uncontracted.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {𝓕 : FieldSpecification} in
variable {n : ℕ} (c : WickContraction n) in
/-- Given a Wick contraction `WickContraction n.succ` and a `i : Fin n.succ` the Wick contraction associated with `n` obtained by removing `i`. If `i` is contracted with `j` in the new Wick contraction `j` will be uncontracted. -/
def WickContraction.erase (c : WickContraction n.succ) (i : Fin n.succ) : WickContraction n := by
  refine ⟨Finset.filter (fun x => Finset.map i.succAboveEmb x ∈ c.1) Finset.univ, ?_, ?_⟩
  · intro a ha
    simpa using c.2.1 (Finset.map i.succAboveEmb a) (by simpa using ha)
  · intro a ha b hb
    simp only [Nat.succ_eq_add_one, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    rw [← Finset.disjoint_map i.succAboveEmb, ← (Finset.map_injective i.succAboveEmb).eq_iff]
    exact c.2.2 _ ha _ hb

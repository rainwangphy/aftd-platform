import AFTD.Prelude
import AFTD.Kb.Physics.WickContraction
import AFTD.Kb.Physics.WickContractionGetDual
import AFTD.Kb.Physics.WickContractionErase
import AFTD.Kb.Physics.WickContractionUncontracted
import AFTD.Kb.Physics.WickContractionMemUncontractedIffNotContracted
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
# WickContraction.mem_not_eq_erase_of_isNone

Topic: quantum_field_theory   Node: e25d25ed6d8b

Provenance: formalization of a published result. Source: Physlib, `WickContraction.mem_not_eq_erase_of_isNone`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/WickContraction/Erase.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

WickContraction.mem_not_eq_erase_of_isNone
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open WickContraction in
variable {𝓕 : FieldSpecification} in
variable {n : ℕ} (c : WickContraction n) in
lemma WickContraction.mem_not_eq_erase_of_isNone (c : WickContraction n.succ) (i : Fin n.succ)
    (h : (c.getDual? i).isNone) (ha : a ∈ c.1) :
    ∃ a', a' ∈ (c.erase i).1 ∧ a = Finset.map i.succAboveEmb a' := by
  have h2a := c.2.1 a ha
  rw [@Finset.card_eq_two] at h2a
  obtain ⟨x, y, hx,hy⟩ := h2a
  subst hy
  have hi : i ∈ c.uncontracted := by
    simp only [Nat.succ_eq_add_one, uncontracted, Finset.mem_filter, Finset.mem_univ, true_and]
    simp_all only [Nat.succ_eq_add_one, Option.isNone_iff_eq_none, ne_eq]
  rw [@mem_uncontracted_iff_not_contracted] at hi
  have hxn : ¬ x = i := by
    by_contra hx
    subst hx
    exact hi {x, y} ha (by simp)
  have hyn : ¬ y = i := by
    by_contra hy
    subst hy
    exact hi {x, y} ha (by simp)
  simp only [Nat.succ_eq_add_one, ← Fin.exists_succAbove_eq_iff] at hxn hyn
  obtain ⟨x', hx'⟩ := hxn
  obtain ⟨y', hy'⟩ := hyn
  use {x', y'}
  subst hx' hy'
  simp only [erase, Nat.succ_eq_add_one, Finset.mem_filter, Finset.mem_univ, Finset.map_insert,
    Fin.succAboveEmb_apply, Finset.map_singleton, true_and, and_true]
  exact ha

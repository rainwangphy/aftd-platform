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
import AFTD.Kb.Physics.WickContractionInstDecidableEq
import AFTD.Kb.GameTheoryEconomics.PermCardLeftGtLe
import AFTD.Kb.GameTheoryEconomics.CatchUpBestMapNeLossIff
import AFTD.Kb.GameTheoryEconomics.CatchUpValueTripleWinOfSumLt
import AFTD.Kb.GameTheoryEconomics.MxsFairImpProp1FairOfSubmodular

/-!
# WickContraction.fromInvolution

Topic: quantum_field_theory   Node: 4f72eebe934f

Provenance: formalization of a published result. Source: Physlib, `WickContraction.fromInvolution`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/WickContraction/Involutions.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Wick contraction formed by an involution `f` of `Fin n` by taking as the contracted sets of the contraction the orbits of `f` of cardinality `2`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {𝓕 : FieldSpecification} in
variable {n : ℕ} (c : WickContraction n) in
/-- The Wick contraction formed by an involution `f` of `Fin n` by taking as the contracted sets of the contraction the orbits of `f` of cardinality `2`. -/
def WickContraction.fromInvolution (f : {f : Fin n → Fin n // Function.Involutive f}) : WickContraction n :=
  ⟨Finset.univ.filter (fun a => a.card = 2 ∧ ∃ i, {i, f.1 i} = a), by
  intro a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, and_imp, forall_exists_index]
  intro h1 _ _
  exact h1, by
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  obtain ⟨i, hai⟩ := ha.2
  subst hai
  obtain ⟨j, hbj⟩ := hb.2
  subst hbj
  by_cases h : i = j
  · subst h
    simp
  · by_cases hi : i = f.1 j
    · subst hi
      simp only [Finset.disjoint_insert_right, Finset.mem_insert, Finset.mem_singleton, not_or,
        Finset.disjoint_singleton_right, true_or, not_true_eq_false, and_false, or_false]
      rw [f.2]
      rw [@Finset.pair_comm]
    · apply Or.inr
      simp only [Finset.disjoint_insert_right, Finset.mem_insert, Finset.mem_singleton, not_or,
        Finset.disjoint_singleton_right]
      apply And.intro
      · apply And.intro
        · exact fun a => h a.symm
        · by_contra hn
          subst hn
          rw [f.2 i] at hi
          simp at hi
      · apply And.intro
        · exact fun a => hi a.symm
        · rw [Function.Injective.eq_iff]
          exact fun a => h (id (Eq.symm a))
          exact Function.Involutive.injective f.2⟩

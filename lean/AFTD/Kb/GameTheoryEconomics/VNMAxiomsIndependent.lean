import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Lottery
import AFTD.Kb.GameTheoryEconomics.VNMCompleteness
import AFTD.Kb.GameTheoryEconomics.VNMTransitivity
import AFTD.Kb.GameTheoryEconomics.VNMIndependence
import AFTD.Kb.GameTheoryEconomics.VNMContinuity
import AFTD.Kb.GameTheoryEconomics.VNMNotCompleteCompletenessIndependent
import AFTD.Kb.GameTheoryEconomics.VNMNotTransitiveTransitivityIndependent
import AFTD.Kb.GameTheoryEconomics.VNMNotIndependentIndependenceIndependent
import AFTD.Kb.GameTheoryEconomics.VNMNotContinuousContinuityIndependent
import AFTD.Kb.Optimization.StdSimplexMixApply

/-!
# VNM.axioms_independent

Topic: general_equilibrium   Node: fc8892c5ff76

Provenance: formalization of a published result. Source: EconCSLib, `VNM.axioms_independent`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/VNMAxioms.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Exercise 2.5 [MSZ]**: The four vNM axioms are independent. For each axiom, there exists a preference relation on lotteries that violates that axiom while satisfying the other three.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
open VNM in
/-- **Exercise 2.5 [MSZ]**: The four vNM axioms are independent. For each axiom, there exists a preference relation on lotteries that violates that axiom while satisfying the other three. -/
theorem VNM.axioms_independent :
    -- ¬Complete
    (∃ pref : Lottery ℚ (Fin 3) → Lottery ℚ (Fin 3) → Prop,
      ¬ Completeness pref ∧ Transitivity pref ∧ Independence pref ∧ Continuity pref) ∧
    -- ¬Transitive
    (∃ pref : Lottery ℚ (Fin 3) → Lottery ℚ (Fin 3) → Prop,
      ¬ Transitivity pref ∧ Completeness pref ∧ Independence pref ∧ Continuity pref) ∧
    -- ¬Independent
    (∃ pref : Lottery ℚ (Fin 3) → Lottery ℚ (Fin 3) → Prop,
      ¬ Independence pref ∧ Completeness pref ∧ Transitivity pref ∧ Continuity pref) ∧
    -- ¬Continuous
    (∃ pref : Lottery ℚ (Fin 3) → Lottery ℚ (Fin 3) → Prop,
      ¬ Continuity pref ∧ Completeness pref ∧ Transitivity pref ∧ Independence pref) :=
  ⟨NotComplete.completeness_independent,
   NotTransitive.transitivity_independent,
   NotIndependent.independence_independent,
   NotContinuous.continuity_independent⟩

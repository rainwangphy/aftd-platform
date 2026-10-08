import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Lottery
import AFTD.Kb.GameTheoryEconomics.VNMCompleteness
import AFTD.Kb.GameTheoryEconomics.VNMTransitivity
import AFTD.Kb.GameTheoryEconomics.VNMIndependence
import AFTD.Kb.GameTheoryEconomics.VNMContinuity
import AFTD.Kb.GameTheoryEconomics.VNMNotCompletePref
import AFTD.Kb.GameTheoryEconomics.VNMNotCompleteNotComplete
import AFTD.Kb.GameTheoryEconomics.VNMNotCompleteTransitive
import AFTD.Kb.GameTheoryEconomics.VNMNotCompleteIndependent
import AFTD.Kb.GameTheoryEconomics.VNMNotCompleteContinuous
import AFTD.Kb.Optimization.StdSimplexMixApply

/-!
# VNM.NotComplete.completeness_independent

Topic: general_equilibrium   Node: c233ab636660

Provenance: formalization of a published result. Source: EconCSLib, `VNM.NotComplete.completeness_independent`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/VNMAxioms.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

VNM.NotComplete.completeness_independent
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
open VNM in
theorem VNM.NotComplete.completeness_independent :
    ∃ pref : Lottery ℚ (Fin 3) → Lottery ℚ (Fin 3) → Prop,
      ¬ Completeness pref ∧ Transitivity pref ∧
      Independence pref ∧ Continuity pref :=
  ⟨pref, not_complete, transitive, independent, continuous⟩

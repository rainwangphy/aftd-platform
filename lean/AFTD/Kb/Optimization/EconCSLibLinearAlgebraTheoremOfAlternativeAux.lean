import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraIsFeasible
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraHasCertificate
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraTheoremOfAlternativeBase
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFMRowIndex
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraZeroRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraPosRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraNegRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmA
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmB
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFeasibleOfFmFeasible
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmCertLift
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFeasCertDisjoint
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmAInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmAInr
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmBInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmBInr
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraRowEvalDef
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCoeffWeightedInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCoeffWeightedInr

/-!
# EconCSLib.LinearAlgebra.theorem_of_alternative_aux

Topic: lp_duality   Node: d2a7faa82e09

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.theorem_of_alternative_aux`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/FourierMotzkin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

EconCSLib.LinearAlgebra.theorem_of_alternative_aux
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
theorem EconCSLib.LinearAlgebra.theorem_of_alternative_aux :
    ∀ (n : ℕ) {I : Type*} [Fintype I] [DecidableEq I]
      (A : I → Fin n → 𝕜) (b : I → 𝕜),
      ¬ IsFeasible A b ↔ HasCertificate A b := by
  intro n
  induction n with
  | zero =>
      intro I _ _ A b
      exact theorem_of_alternative_base A b
  | succ n ih =>
      intro I _ _ A b
      refine ⟨?_, fun hcert hfeas => feas_cert_disjoint A b hfeas hcert⟩
      intro hinf
      have h_red_inf : ¬ IsFeasible (fmA A) (fmB A b) :=
        fun h => hinf (feasible_of_fm_feasible A b h)
      have h_red_cert : HasCertificate (fmA A) (fmB A b) :=
        (ih (fmA A) (fmB A b)).mp h_red_inf
      exact fm_cert_lift A b h_red_cert

import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraHasCertificate
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFMRowIndex
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraZeroRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraPosRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraNegRows
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmA
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmB
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraIsCertificate
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCert
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCertNonneg
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCertColumnZeroLast
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCertColumnZeroCastSucc
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCertRhs
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmAInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmAInr
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmBInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraFmBInr
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCoeffWeightedInl
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraLiftCoeffWeightedInr

/-!
# EconCSLib.LinearAlgebra.fm_cert_lift

Topic: lp_duality   Node: 9eb450622f4a

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.fm_cert_lift`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/FourierMotzkin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Farkas certificate lift**: if `u'` certifies the reduced system, `liftCert A u'` certifies the original.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
/-- **Farkas certificate lift**: if `u'` certifies the reduced system, `liftCert A u'` certifies the original. -/
theorem EconCSLib.LinearAlgebra.fm_cert_lift (A : I → Fin (n+1) → 𝕜) (b : I → 𝕜)
    (hred : HasCertificate (fmA A) (fmB A b)) : HasCertificate A b := by
  obtain ⟨u', hu'_nn, hu'_zero, hu'_pos⟩ := hred
  refine ⟨liftCert A u', liftCert_nonneg A hu'_nn, ?_, ?_⟩
  · -- ∀ j : Fin (n+1), ∑ i, u i * A i j = 0
    intro j
    refine Fin.lastCases ?_ ?_ j
    · exact liftCert_column_zero_last A u'
    · intro j'
      exact liftCert_column_zero_castSucc A b hu'_zero j'
  · rw [liftCert_rhs]
    exact hu'_pos

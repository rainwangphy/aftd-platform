import AFTD.Prelude
import AFTD.Kb.Optimization.EconCSLibLinearAlgebraIsCertificate

/-!
# EconCSLib.LinearAlgebra.HasCertificate

Topic: lp_duality   Node: 1be9cb146c28

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.HasCertificate`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/FourierMotzkin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Existence of a Farkas certificate.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Existence of a Farkas certificate. -/
def EconCSLib.LinearAlgebra.HasCertificate {I : Type*} {n : ℕ} [Fintype I] (A : I → Fin n → 𝕜)
    (b : I → 𝕜) : Prop :=
  ∃ u : I → 𝕜, IsCertificate A b u

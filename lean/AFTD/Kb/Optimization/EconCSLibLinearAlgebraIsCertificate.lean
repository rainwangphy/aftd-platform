import AFTD.Prelude

/-!
# EconCSLib.LinearAlgebra.IsCertificate

Topic: lp_duality   Node: bc77a77a5a6d

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearAlgebra.IsCertificate`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearAlgebra/FourierMotzkin.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`u : I → 𝕜` is a Farkas certificate of infeasibility of `A x ≥ b`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- `u : I → 𝕜` is a Farkas certificate of infeasibility of `A x ≥ b`. -/
def EconCSLib.LinearAlgebra.IsCertificate {I : Type*} {n : ℕ} [Fintype I] (A : I → Fin n → 𝕜)
    (b : I → 𝕜) (u : I → 𝕜) : Prop :=
  (∀ i, 0 ≤ u i) ∧
  (∀ j : Fin n, ∑ i, u i * A i j = 0) ∧
  (0 < ∑ i, u i * b i)

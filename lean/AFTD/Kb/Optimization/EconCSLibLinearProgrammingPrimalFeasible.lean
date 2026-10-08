import AFTD.Prelude

/-!
# EconCSLib.LinearProgramming.PrimalFeasible

Topic: lp_duality   Node: c120d11345d0

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearProgramming.PrimalFeasible`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearProgramming/StrongDuality.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Primal feasibility: `∃ x, A x ≥ b ∧ x ≥ 0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
/-- Primal feasibility: `∃ x, A x ≥ b ∧ x ≥ 0`. -/
def EconCSLib.LinearProgramming.PrimalFeasible (A : I → Fin n → 𝕜) (b : I → 𝕜) : Prop :=
  ∃ x : Fin n → 𝕜, (∀ i, b i ≤ ∑ j, A i j * x j) ∧ (∀ j, 0 ≤ x j)

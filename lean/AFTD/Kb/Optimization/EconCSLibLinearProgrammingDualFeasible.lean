import AFTD.Prelude

/-!
# EconCSLib.LinearProgramming.DualFeasible

Topic: lp_duality   Node: b1b94a17784c

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.LinearProgramming.DualFeasible`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/LinearProgramming/StrongDuality.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Dual feasibility of `u`: `u ≥ 0 ∧ uᵀA ≤ c`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] [DecidableEq I] {n : ℕ} in
/-- Dual feasibility of `u`: `u ≥ 0 ∧ uᵀA ≤ c`. -/
def EconCSLib.LinearProgramming.DualFeasible (A : I → Fin n → 𝕜) (c : Fin n → 𝕜) (u : I → 𝕜) : Prop :=
  (∀ i, 0 ≤ u i) ∧ (∀ j, ∑ i, u i * A i j ≤ c j)

import AFTD.Prelude

/-!
# MinimaxLoomis.dropEquiv

Topic: equilibria   Node: abcd9dde7210

Provenance: formalization of a published result. Source: EconCSLib, `MinimaxLoomis.dropEquiv`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/MinimaxLoomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The equivalence `J ≃ Option {j // j ≠ j₀}`: `j₀ ↦ none`, other `j ↦ some j`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- The equivalence `J ≃ Option {j // j ≠ j₀}`: `j₀ ↦ none`, other `j ↦ some j`. -/
noncomputable def MinimaxLoomis.dropEquiv [DecidableEq J] (j₀ : J) : J ≃ Option {j : J // j ≠ j₀} where
  toFun j := if h : j = j₀ then none else some ⟨j, h⟩
  invFun o := match o with | none => j₀ | some j => j.val
  left_inv j := by by_cases h : j = j₀ <;> simp [h]
  right_inv o := by cases o with
    | none => simp
    | some j => simp [j.property]

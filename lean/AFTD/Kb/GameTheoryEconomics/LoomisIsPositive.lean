import AFTD.Prelude

/-!
# Loomis.IsPositive

Topic: equilibria   Node: c8400dbeb536

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.IsPositive`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A matrix `B : I → J → ℝ` is **entrywise positive** if every entry is `> 0`. This is the hypothesis driving the general Loomis theorem, and the only property of `B` the proof needs.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- A matrix `B : I → J → ℝ` is **entrywise positive** if every entry is `> 0`. This is the hypothesis driving the general Loomis theorem, and the only property of `B` the proof needs. -/
def Loomis.IsPositive (B : I → J → ℝ) : Prop := ∀ i j, 0 < B i j

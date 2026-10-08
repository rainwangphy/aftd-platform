import AFTD.Prelude

/-!
# EconCSLib.StrategicGame.IsStochasticMatrix

Topic: equilibria   Node: 1321442d8e4a

Provenance: formalization of a published result. Source: EconCSLib, `EconCSLib.StrategicGame.IsStochasticMatrix`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/StochasticMatrix.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A finite (row-)**stochastic matrix**: entries are non-negative and each row sums to `1`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I : Type} [Fintype I] [Nonempty I] [DecidableEq I] in
/-- A finite (row-)**stochastic matrix**: entries are non-negative and each row sums to `1`. -/
structure EconCSLib.StrategicGame.IsStochasticMatrix (A : I → I → ℝ) : Prop where
  nonneg : ∀ i j, 0 ≤ A i j
  rowSum : ∀ i, ∑ j, A i j = 1

import AFTD.Prelude

/-!
# ZeroSumGame

Topic: equilibria   Node: 4742a9ba60c9

Provenance: formalization of a published result. Source: TCSlib, `ZeroSumGame`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ZeroSumGame.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A \emph{finite two-player zero-sum game} with $M$ row actions and $N$ column
actions is a record consisting of a payoff matrix $A : \mathrm{Fin}\,M \to
\mathrm{Fin}\,N \to \mathbb{R}$ together with proofs that every entry satisfies
$0 \le A_{ij} \le 1$.  The row player seeks to maximise the payoff; the column
player seeks to minimise it.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- A finite two-player zero-sum game with `M` row actions and `N` column actions, given by a payoff matrix with entries in the interval `[0, 1]`. The row player wants larger payoffs; the column player wants smaller payoffs. [CBL06, §7.1]; [FS99, §2]. Deviation: FS99's `M(i, j)` is the row player's loss (row minimizes); here entries are payoffs and the row player maximizes. Entries are in `[0, 1]` as in FS99 (CBL06 allows general bounded payoffs). -/
structure ZeroSumGame (M N : ℕ) where
  payoff : Fin M → Fin N → ℝ
  payoff_nonneg : ∀ i j, 0 ≤ payoff i j
  payoff_le_one : ∀ i j, payoff i j ≤ 1

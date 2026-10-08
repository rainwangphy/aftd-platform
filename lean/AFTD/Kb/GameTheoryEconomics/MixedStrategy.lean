import AFTD.Prelude

/-!
# MixedStrategy

Topic: equilibria   Node: 1107c6e6fc5d

Provenance: formalization of a published result. Source: TCSlib, `MixedStrategy`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ZeroSumGame.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A \emph{mixed strategy} over $n$ actions is a record consisting of a weight
function $w : \mathrm{Fin}\,n \to \mathbb{R}$ together with proofs that every
weight is non-negative and that the weights sum to $1$, i.e.\ $w$ is a
probability distribution over $\mathrm{Fin}\,n$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- A mixed strategy over `n` pure actions: a probability distribution on `Fin n`, kept as an explicit weight vector together with nonnegativity and the sum-to-one law. [CBL06, §7.1]; [FS99, §2]. This is enough for finite games and avoids extra simplex infrastructure. -/
structure MixedStrategy (n : ℕ) where
  weights : Fin n → ℝ
  nonneg : ∀ i, 0 ≤ weights i
  sum_one : ∑ i : Fin n, weights i = 1

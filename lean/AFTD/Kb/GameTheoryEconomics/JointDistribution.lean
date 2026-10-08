import AFTD.Prelude

/-!
# JointDistribution

Topic: equilibria   Node: 9d22f3c31511

Provenance: formalization of a published result. Source: TCSlib, `JointDistribution`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/CCE.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A joint distribution $\sigma$ on $\mathrm{Fin}\,M \times \mathrm{Fin}\,N$ is a
nonnegative function $\sigma_{ij} \ge 0$ satisfying
$\sum_{i,j} \sigma_{ij} = 1$.  It represents a correlated distribution over
pure action profiles of the two players.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BigOperators in
/-- A probability distribution over action profiles `Fin M × Fin N`, given as a nonnegative weight for each profile `(i, j)` with total mass one. [Rou13-L13, Def. 3.4]. -/
structure JointDistribution (M N : ℕ) where
  /-- The probability of the action profile `(i, j)`. -/
  prob : Fin M → Fin N → ℝ
  /-- Every profile probability is nonnegative. -/
  nonneg : ∀ i j, 0 ≤ prob i j
  /-- The profile probabilities sum to one. -/
  sum_one : ∑ i : Fin M, ∑ j : Fin N, prob i j = 1

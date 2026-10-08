import AFTD.Prelude

/-!
# Game

Topic: equilibria   Node: d42b2db96b52

Provenance: formalization of a published result. Source: TCSlib, `Game`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/CCE.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A finite two-player game with $M$ row actions and $N$ column actions, specified
by a row utility function $u_r : \mathrm{Fin}\,M \times \mathrm{Fin}\,N \to \mathbb{R}$
and a column utility function $u_c : \mathrm{Fin}\,M \times \mathrm{Fin}\,N \to \mathbb{R}$.
Both players are utility maximizers.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BigOperators in
/-- A finite two-player game with `M` row actions and `N` column actions, specified by separate utility functions for the row and column players. Both players are maximizers. [Rou13-L13, §3.1]. Deviation: the source's games are cost-minimization games; here both players maximize. -/
structure Game (M N : ℕ) where
  /-- The row player's utility at the action profile `(i, j)`. -/
  rowUtility : Fin M → Fin N → ℝ
  /-- The column player's utility at the action profile `(i, j)`. -/
  colUtility : Fin M → Fin N → ℝ

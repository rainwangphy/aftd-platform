import AFTD.Prelude

/-!
# Kruskal.WEdge

Topic: graphs   Node: b73ec522e173

Provenance: formalization of a published result. Source: TCSlib, `Kruskal.WEdge`. Lean proof by Harsha Polavaram, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Basic.lean (Copyright (c) 2026 Harsha Polavaram. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A \emph{weighted edge} over $n$ vertices is a structure with two endpoints
$u, v : \mathrm{Fin}\,n$ and a natural-number weight $w : \mathbb{N}$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
structure Kruskal.WEdge (n : ℕ) where
  u : Fin n
  v : Fin n
  weight : ℕ
  deriving Repr, DecidableEq

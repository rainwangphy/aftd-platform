import AFTD.Prelude

/-!
# Kruskal.UF

Topic: graphs   Node: 25884c02ee5f

Provenance: formalization of a published result. Source: TCSlib, `Kruskal.UF`. Lean proof by Harsha Polavaram, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Basic.lean (Copyright (c) 2026 Harsha Polavaram. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The union-find state for $n$ nodes is defined as a function
$\mathrm{Fin}\,n \to \mathbb{N}$ mapping each node to its current
representative (component label).
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
def Kruskal.UF (n : ℕ) := Fin n → ℕ

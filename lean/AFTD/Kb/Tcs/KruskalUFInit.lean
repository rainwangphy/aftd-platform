import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalUF

/-!
# Kruskal.UF.init

Topic: graphs   Node: 05302796fdac

Provenance: formalization of a published result. Source: TCSlib, `Kruskal.UF.init`. Lean proof by Harsha Polavaram, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Basic.lean (Copyright (c) 2026 Harsha Polavaram. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

$\mathtt{init}\,n$ constructs the identity union-find on $n$ nodes: every node
$i$ is its own representative, i.e.\ $\mathtt{init}\,n\,(i) = i$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
def Kruskal.UF.init (n : ℕ) : UF n := fun i => i.val

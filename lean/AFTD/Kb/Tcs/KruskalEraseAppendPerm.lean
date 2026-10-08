import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalWEdge

/-!
# Kruskal.erase_append_perm

Topic: graphs   Node: 22bc2820849e

Provenance: helper lemma. TCSlib, `Kruskal.erase_append_perm`. Lean proof by Harsha Polavaram, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/UnionFind.lean (Copyright (c) 2026 Harsha Polavaram. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Moving a member to the end is a permutation. Let $l$ be a finite list of weighted edges over $n$ vertices, and let $e$ be a weighted
edge that occurs in $l$. Then $l$ is a permutation of the list obtained by deleting the
first occurrence of $e$ from $l$ and appending $e$ at the end.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
lemma Kruskal.erase_append_perm {n : ℕ} {l : List (WEdge n)} {e : WEdge n} (he : e ∈ l) :
    l.Perm (l.erase e ++ [e]) := by grind

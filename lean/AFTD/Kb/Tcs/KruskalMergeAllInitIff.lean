import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalUFInit
import AFTD.Kb.Tcs.KruskalUFMergeAll
import AFTD.Kb.Tcs.KruskalWEdge
import AFTD.Kb.Tcs.KruskalReach
import AFTD.Kb.Tcs.KruskalSymAdj
import AFTD.Kb.Tcs.KruskalMergeAllIffReach
import AFTD.Kb.Tcs.KruskalUFInitFind
import AFTD.Kb.Tcs.KruskalUFFindDef

/-!
# Kruskal.mergeAll_init_iff

Topic: graphs   Node: 8dd1f8bf4711

Provenance: helper lemma. TCSlib, `Kruskal.mergeAll_init_iff`. Lean proof by Harsha Polavaram, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/UnionFind.lean (Copyright (c) 2026 Harsha Polavaram. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Correctness of union-find merging from the initial state. Fix a natural number $n$, and let $\mathit{edges}$ be a list of weighted edges on the
vertex set $\mathrm{Fin}\,n$. Consider the union-find state obtained by starting from
the initial state on $n$ nodes, in which every node is its own representative, and
processing $\mathit{edges}$ in order, so that at each weighted edge the components of
the two endpoints of that edge are merged. Then, for any two vertices $a, b \in
\mathrm{Fin}\,n$, the vertices $a$ and $b$ carry the same representative in the
resulting state if and only if $a$ and $b$ are connected by a path through the edges of
$\mathit{edges}$ — equivalently, if and only if the reflexive--transitive closure of
symmetric adjacency along $\mathit{edges}$ relates $a$ to $b$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
lemma Kruskal.mergeAll_init_iff {n : ℕ} (edges : List (WEdge n)) (a b : Fin n) :
    (UF.init n).mergeAll edges a = (UF.init n).mergeAll edges b ↔ Reach edges a b := by
  convert mergeAll_iff_reach (UF.init n) [] edges _ a b
  · rfl
  intro a b; constructor <;> intro h <;> simp_all +decide [Reach]
  · cases a; cases b; aesop
  · induction h <;> simp_all +decide [SymAdj]

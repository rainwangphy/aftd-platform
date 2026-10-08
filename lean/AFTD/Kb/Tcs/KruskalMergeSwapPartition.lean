import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalUF
import AFTD.Kb.Tcs.KruskalUFSamePartition
import AFTD.Kb.Tcs.KruskalUFMerge
import AFTD.Kb.Tcs.KruskalWEdge
import AFTD.Kb.Tcs.KruskalUFFindDef

/-!
# Kruskal.merge_swap_partition

Topic: graphs   Node: 568406033aba

Provenance: helper lemma. TCSlib, `Kruskal.merge_swap_partition`. Lean proof by Harsha Polavaram, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/UnionFind.lean (Copyright (c) 2026 Harsha Polavaram. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Merge order is irrelevant to the induced partition. Let $n$ be a natural number, let $\mathit{uf}\colon \mathrm{Fin}\,n \to \bbn$ be a
union-find state, and let $a$ and $b$ be weighted edges over $n$ vertices, with
endpoints $a_u, a_v$ and $b_u, b_v$ respectively. Form one state by merging the
components of $a_u$ and $a_v$ and then merging the components of $b_u$ and $b_v$, and a
second state by performing these two merges in the opposite order. Then the two
resulting states induce the same partition of the nodes: for all $i, j :
\mathrm{Fin}\,n$, the first state assigns $i$ and $j$ the same representative if and
only if the second state does.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
lemma Kruskal.merge_swap_partition {n : ℕ} (uf : UF n) (a b : WEdge n) :
    UF.SamePartition
      ((uf.merge a.u a.v).merge b.u b.v)
      ((uf.merge b.u b.v).merge a.u a.v) := by
  intros i j
  by_cases hi : uf i = uf a.u <;> by_cases hj : uf j = uf a.u <;>
    simp +decide [*, UF.merge] <;> grind

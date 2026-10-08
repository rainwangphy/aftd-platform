import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalUF
import AFTD.Kb.Tcs.KruskalUFSamePartition
import AFTD.Kb.Tcs.KruskalUFMerge
import AFTD.Kb.Tcs.KruskalUFMergeAll
import AFTD.Kb.Tcs.KruskalWEdge
import AFTD.Kb.Tcs.KruskalUFSamePartitionRfl
import AFTD.Kb.Tcs.KruskalUFFindDef

/-!
# Kruskal.mergeAll_cons_eq

Topic: graphs   Node: 79d777f9bfa1

Provenance: helper lemma. TCSlib, `Kruskal.mergeAll_cons_eq`. Lean proof by Harsha Polavaram, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/UnionFind.lean (Copyright (c) 2026 Harsha Polavaram. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Peeling the leading edge off a merge fold. Let $\mathit{uf} : \mathrm{Fin}\,n \to \bbn$ be a union-find state on $n$ nodes, let $e$
be a weighted edge with endpoints $u$ and $v$ over these nodes, and let $S$ be a list of
weighted edges over the same nodes. Folding the list $e :: S$ into $\mathit{uf}$ and
folding the list $S$ into the union-find state that merges the components of $u$ and $v$
in $\mathit{uf}$ induce the same partition of the nodes: for all nodes $i$ and $j$,
folding $e :: S$ into $\mathit{uf}$ assigns $i$ and $j$ a common representative if and
only if folding $S$ into the merge of $u$ and $v$ assigns $i$ and $j$ a common
representative.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
lemma Kruskal.mergeAll_cons_eq {n : ℕ} (uf : UF n) (e : WEdge n) (S : List (WEdge n)) :
    UF.SamePartition (uf.mergeAll (e :: S)) ((uf.merge e.u e.v).mergeAll S) :=
  UF.SamePartition.rfl _

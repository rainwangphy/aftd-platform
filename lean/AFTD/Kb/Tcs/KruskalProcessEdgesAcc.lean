import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalUF
import AFTD.Kb.Tcs.KruskalUFMerge
import AFTD.Kb.Tcs.KruskalWEdge
import AFTD.Kb.Tcs.KruskalProcessEdges
import AFTD.Kb.Tcs.KruskalUFFindDef

/-!
# Kruskal.processEdges_acc

Topic: graphs   Node: d99db94d47ab

Provenance: helper lemma. TCSlib, `Kruskal.processEdges_acc`. Lean proof by Harsha Polavaram, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Optimality.lean (Copyright (c) 2026 Harsha Polavaram. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Accumulator splits off as a reversed prefix. Fix $n \in \bbn$, and let $\mathit{es}$ be a list of weighted edges over $n$ vertices,
$\mathit{uf}$ a union-find state on $n$ nodes, and $\mathit{acc}$ a list of weighted
edges over $n$ vertices. Then running the edge-selection sweep on $\mathit{es}$ from
state $\mathit{uf}$ with initial accumulator $\mathit{acc}$ yields the reversal of
$\mathit{acc}$ concatenated (on the left) with the result of running the same sweep on
$\mathit{es}$ from the same state $\mathit{uf}$ but with the empty accumulator.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
lemma Kruskal.processEdges_acc {n : ℕ} (edges : List (WEdge n)) (uf : UF n)
    (acc : List (WEdge n)) :
    processEdges edges uf acc = acc.reverse ++ processEdges edges uf [] := by
  induction edges generalizing uf acc with
  | nil => simp [processEdges]
  | cons e edges ih =>
    simp only [processEdges]
    split_ifs with h
    · rw [ih (uf.merge e.u e.v) (e :: acc), ih (uf.merge e.u e.v) [e]]; simp
    · exact ih uf acc

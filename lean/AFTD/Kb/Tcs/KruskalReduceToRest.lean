import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalMergeNoop
import AFTD.Kb.Tcs.KruskalUFSamePartitionTrans
import AFTD.Kb.Tcs.KruskalUF
import AFTD.Kb.Tcs.KruskalUFSamePartitionRfl
import AFTD.Kb.Tcs.KruskalTotalWeightNil
import AFTD.Kb.Tcs.KruskalUFFindDef
import AFTD.Kb.Tcs.KruskalWEdge
import AFTD.Kb.Tcs.KruskalUFSamePartition
import AFTD.Kb.Tcs.KruskalTotalWeight
import AFTD.Kb.Tcs.KruskalUFMerge
import AFTD.Kb.Tcs.KruskalUFMergeAll

/-!
# Kruskal.reduce_to_rest

Topic: graphs   Node: 950a08d9d0fa

Provenance: helper lemma. TCSlib, `Kruskal.reduce_to_rest`. Lean proof by Harsha Polavaram, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Exchange.lean (Copyright (c) 2026 Harsha Polavaram. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Dropping a redundant edge from a candidate set. Let $\mathit{uf}$ be a union-find state on $n$ nodes, let $e$ be a weighted edge with
endpoints $u$ and $v$, and let $\mathit{rest}$ and $S$ be lists of weighted edges.
Suppose every edge of $S$ occurs in the list $e :: \mathit{rest}$ formed by prepending
$e$ to $\mathit{rest}$; that merging all edges of $S$ into $\mathit{uf}$ induces the
same partition of the nodes as merging all edges of $\mathit{rest}$ into $\mathit{uf}$;
and that $e$ is already redundant for $\mathit{uf}$, meaning $\mathit{uf}(u) =
\mathit{uf}(v)$. Then there exists a list $S'$ of weighted edges, every one of which
occurs in $\mathit{rest}$, such that merging all edges of $S'$ into $\mathit{uf}$
induces the same partition as merging all edges of $\mathit{rest}$, and the total weight
of $S'$ is at most the total weight of $S$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
lemma Kruskal.reduce_to_rest {n : ℕ} (uf : UF n) (e : WEdge n) (rest S : List (WEdge n))
    (hSsub : ∀ x ∈ S, x ∈ e :: rest)
    (hSspan : UF.SamePartition (uf.mergeAll S) (uf.mergeAll rest))
    (hred : uf e.u = uf e.v) :
    ∃ S' : List (WEdge n),
      (∀ x ∈ S', x ∈ rest) ∧
      UF.SamePartition (uf.mergeAll S') (uf.mergeAll rest) ∧
      totalWeight S' ≤ totalWeight S := by
  revert hSspan hSsub hred
  have mergeAll_filter_redundant (uf : UF n) (S : List (WEdge n)) (e : WEdge n)
      (rest : List (WEdge n))
      (hSsub : ∀ x ∈ S, x ∈ e :: rest) (hred : uf e.u = uf e.v) :
      UF.SamePartition (uf.mergeAll (S.filter (fun x => decide (x ∈ rest))))
        (uf.mergeAll S) := by
    induction' S with x S ih generalizing uf
    · exact UF.SamePartition.rfl _
    · by_cases hx : x ∈ rest <;> simp_all +decide
      · convert ih (uf.merge x.u x.v) _ using 1
        all_goals first | rfl | (unfold UF.merge; simp [hred])
      · convert ih uf hred using 1
        rw [show uf.mergeAll (e :: S) = (uf.merge e.u e.v).mergeAll S from by rfl]
        rw [merge_noop _ _ _ hred]
  intro hSsub hSspan hred
  refine ⟨S.filter (fun x => decide (x ∈ rest)), ?_, ?_, ?_⟩
  · intro x hx; simp at hx; exact hx.2
  · exact (mergeAll_filter_redundant uf S e rest hSsub hred).trans hSspan
  · unfold totalWeight
    have hle : ∀ l : List (WEdge n),
        (List.map WEdge.weight (l.filter (fun x => decide (x ∈ rest)))).sum ≤
          (List.map WEdge.weight l).sum := by
      intro l
      induction l with
      | nil => simp
      | cons x l ih =>
        by_cases hx : x ∈ rest <;> simp [hx] <;> linarith
    exact hle S

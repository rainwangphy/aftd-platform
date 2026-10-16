import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalUF
import AFTD.Kb.Tcs.KruskalUFSamePartition
import AFTD.Kb.Tcs.KruskalUFMerge
import AFTD.Kb.Tcs.KruskalUFMergeAll
import AFTD.Kb.Tcs.KruskalWEdge
import AFTD.Kb.Tcs.KruskalExchangeWithBase
import AFTD.Kb.Tcs.KruskalReach
import AFTD.Kb.Tcs.KruskalReachLift
import AFTD.Kb.Tcs.KruskalReachMemIff
import AFTD.Kb.Tcs.KruskalReachMono
import AFTD.Kb.Tcs.KruskalReachSymm
import AFTD.Kb.Tcs.KruskalMergeAllIffReach
import AFTD.Kb.Tcs.KruskalUFFindDef
import AFTD.Kb.Tcs.KruskalSymAdj
import AFTD.Kb.Tcs.KruskalUFSamePartitionSymm

/-!
# Kruskal.uf_exchange

Topic: graphs   Node: 439b344753e2

Provenance: helper lemma. TCSlib, `Kruskal.uf_exchange`. Lean proof by Harsha Polavaram, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/Exchange.lean (Copyright (c) 2026 Harsha Polavaram. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Union-find form of the exchange argument. Let $\mathit{uf}\colon \mathrm{Fin}\,n \to \bbn$ be a union-find state whose classes
coincide with the reachability classes of an edge list $\mathit{base}$: for all nodes
$a,b$ one has $\mathit{uf}(a) = \mathit{uf}(b)$ if and only if $a$ and $b$ are joined by
a path through the edges of $\mathit{base}$. Let $S$ be a further list of weighted
edges, and let $e$ be a weighted edge with endpoints $u$ and $v$ such that merging every
edge of $S$ into $\mathit{uf}$ places $u$ and $v$ in a common component, while
$\mathit{uf}$ itself keeps them in distinct components. Then there is an edge $f \in S$
for which the state obtained by first merging $u$ with $v$ and then merging all edges of
$S$ other than $f$ induces the same partition of the nodes as the state obtained by
merging all edges of $S$ into $\mathit{uf}$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
lemma Kruskal.uf_exchange {n : ℕ} (uf : UF n) (base S : List (WEdge n)) (e : WEdge n)
    (huf : ∀ a b : Fin n, uf a = uf b ↔ Reach base a b)
    (hconn : (uf.mergeAll S) e.u = (uf.mergeAll S) e.v)
    (hdiff : uf e.u ≠ uf e.v) :
    ∃ f ∈ S, UF.SamePartition
      ((uf.merge e.u e.v).mergeAll (S.erase f))
      (uf.mergeAll S) := by
  obtain ⟨f, hfS, hswap⟩ : ∃ f ∈ S, ∀ a b, Reach (base ++ S) a b →
      Reach (base ++ S.erase f ++ [e]) a b := by
    apply exchange_with_base
    · exact (mergeAll_iff_reach uf base S huf e.u e.v).mp hconn
    · exact fun h => hdiff <| (huf _ _).2 h
    · contrapose! hdiff; aesop
  have hswap_symm : ∀ a b, Reach (base ++ S.erase f ++ [e]) a b → Reach (base ++ S) a b := by
    intro a b hab
    apply reach_lift (edges := base ++ S.erase f ++ [e]) _ hab
    intro a b ⟨g, hg, hg'⟩
    rcases List.mem_append.mp hg with hg1 | hg1
    · rcases List.mem_append.mp hg1 with hg2 | hg2
      · exact reach_mono (.single ⟨g, hg2, hg'⟩) (fun x hx => List.mem_append_left _ hx)
      · exact reach_mono (.single ⟨g, List.mem_of_mem_erase hg2, hg'⟩)
              (fun x hx => List.mem_append_right _ hx)
    · have hge : e = g := (List.mem_singleton.mp hg1).symm
      subst hge
      have hreach_e : Reach (base ++ S) e.u e.v :=
        (mergeAll_iff_reach uf base S huf e.u e.v).mp hconn
      rcases hg' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hreach_e
      · exact reach_symm hreach_e
  have hcomp_S : ∀ a b, (uf.mergeAll S) a = (uf.mergeAll S) b ↔ Reach (base ++ S) a b :=
    mergeAll_iff_reach uf base S huf
  have hcomp_S' : ∀ a b, ((uf.merge e.u e.v).mergeAll (S.erase f)) a =
      ((uf.merge e.u e.v).mergeAll (S.erase f)) b ↔ Reach (base ++ S.erase f ++ [e]) a b := by
    have hcomp_e : ∀ a b, ((uf.merge e.u e.v).mergeAll (S.erase f)) a =
        ((uf.merge e.u e.v).mergeAll (S.erase f)) b ↔ Reach (base ++ [e] ++ S.erase f) a b := by
      apply mergeAll_iff_reach
      exact mergeAll_iff_reach uf base [e] huf
    simp_all +decide [List.append_assoc]
    apply reach_mem_iff; grind
  exact ⟨f, hfS, fun a b => by aesop⟩

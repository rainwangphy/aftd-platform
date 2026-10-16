import AFTD.Prelude
import AFTD.Kb.Tcs.KruskalUF
import AFTD.Kb.Tcs.KruskalUFMerge
import AFTD.Kb.Tcs.KruskalUFMergeAll
import AFTD.Kb.Tcs.KruskalWEdge
import AFTD.Kb.Tcs.KruskalReach
import AFTD.Kb.Tcs.KruskalReachConsIff
import AFTD.Kb.Tcs.KruskalReachMono
import AFTD.Kb.Tcs.KruskalReachSymm
import AFTD.Kb.Tcs.KruskalUFFindDef
import AFTD.Kb.Tcs.KruskalSymAdj

/-!
# Kruskal.mergeAll_iff_reach

Topic: graphs   Node: 961d8e2718ec

Provenance: helper lemma. TCSlib, `Kruskal.mergeAll_iff_reach`. Lean proof by Harsha Polavaram, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/GraphTheory/Kruskal/UnionFind.lean (Copyright (c) 2026 Harsha Polavaram. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Merging preserves the reachability invariant. Fix $n$ and let $uf : \mathrm{Fin}\,n \to \bbn$ be a union-find state assigning each of
the $n$ nodes a representative. Let $\mathit{base}$ and $\mathit{edges}$ be lists of
weighted edges on these $n$ vertices, and suppose $uf$ already encodes reachability
along $\mathit{base}$, in the sense that for all nodes $a, b$ one has $uf(a) = uf(b)$ if
and only if $a$ and $b$ are connected by a path through the edges of $\mathit{base}$.
Then, writing $uf'$ for the state obtained by merging the endpoints of every edge of
$\mathit{edges}$ into $uf$ in order, for all nodes $a, b$ one has $uf'(a) = uf'(b)$ if
and only if $a$ and $b$ are connected by a path through the edges of the concatenated
list $\mathit{base} \mathbin{+\!\!+} \mathit{edges}$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
lemma Kruskal.mergeAll_iff_reach {n : ℕ} (uf : UF n) (base edges : List (WEdge n))
    (huf : ∀ a b : Fin n, uf a = uf b ↔ Reach base a b) (a b : Fin n) :
    (uf.mergeAll edges) a = (uf.mergeAll edges) b ↔ Reach (base ++ edges) a b := by
  induction' edges with e edges ih generalizing uf base
  · convert huf a b using 1 <;> try rfl
    simp +decide [Reach]
  · convert ih (uf.merge e.u e.v) (base ++ [e]) _ using 1
    · rfl
    · simp +decide [List.append_assoc]
    · intro a b; constructor <;> intro h <;> simp_all +decide [UF.merge]
      · split_ifs at h <;> simp_all +decide
        · have h_reach_base : Reach base a b :=
            (‹Reach base a e.v›).trans (reach_symm ‹Reach base b e.v›)
          exact reach_mono h_reach_base fun x hx => by aesop
        · have h_reach : Reach (base ++ [e]) a e.v ∧ Reach (base ++ [e]) e.u b :=
            ⟨reach_mono ‹_› fun x hx => List.mem_append_left _ hx,
             reach_mono ‹_› fun x hx => List.mem_append_left _ hx⟩
          have h_ev_eu : Reach (base ++ [e]) e.v e.u :=
            Relation.ReflTransGen.single ⟨e, by simp +decide, by simp +decide⟩
          exact h_reach.1.trans (h_ev_eu.trans h_reach.2)
        · have h_au : Reach (base ++ [e]) a e.u :=
            reach_mono h fun x hx => by aesop
          have h_euv : Reach (base ++ [e]) e.u e.v :=
            Relation.ReflTransGen.single ⟨e, by aesop⟩
          have h_vb : Reach (base ++ [e]) e.v b :=
            reach_symm <| reach_mono ‹_› fun x hx => by aesop
          exact h_au.trans (h_euv.trans h_vb)
        · exact reach_mono h fun x hx => List.mem_append_left _ hx
      · have h_reach : Reach base a b ∨ (Reach base a e.u ∧ Reach base e.v b) ∨
            (Reach base a e.v ∧ Reach base e.u b) := by
          convert reach_cons_iff.mp _
          convert reach_mono h _ using 1
          grind
        grind

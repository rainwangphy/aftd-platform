import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphQuasikernelOnSubset

/-!
# digraph_kernel_perfect_subset_quasikernel_cover

Topic: graphs   Node: 0f7bf3c55a84

Provenance: formalization of a published result. Source: Lemma 14 of A Variable Version of the Quasi-Kernel Conjecture, https://www.combinatorics.org/ojs/index.php/eljc/article/download/v32i2p53/pdf/; all arcs reversed and the external-neighborhood convention made explicit.

Let D be a finite directed graph, allowing loops. Call a vertex set independent when there is no arc between any two distinct vertices in it, so a loop does not prevent independence. Suppose every subset of S has an independent subset that contains or has an arc to each vertex of that subset. Then D has an independent set Q from which every vertex is reachable in at most two steps, every vertex of S belongs to Q or is reached from Q in one step, and no vertex of Q outside S is reached in one step from S.
-/

theorem digraph_kernel_perfect_subset_quasikernel_cover
    {α : Type} [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj] (S : Finset α)
    (hkernel : ∀ T : Finset α, T ⊆ S → ∃ K : Finset α,
      K ⊆ T ∧
      (∀ u ∈ K, ∀ v ∈ K, u ≠ v → ¬ D.Adj u v) ∧
      (∀ v ∈ T, ∃ u ∈ K, u = v ∨ D.Adj u v)) :
    ∃ Q : Finset α,
      (∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → ¬ D.Adj u v) ∧
      (∀ v, ∃ u ∈ Q, u = v ∨ D.Adj u v ∨ ∃ w, D.Adj u w ∧ D.Adj w v) ∧
      (∀ s ∈ S, ∃ q ∈ Q, q = s ∨ D.Adj q s) ∧
      (∀ v ∈ Q, v ∉ S → ¬ ∃ s ∈ S, D.Adj s v) := by
  classical
  let T := Finset.univ.filter fun x => x ∉ S ∧ ¬ ∃ s ∈ S, D.Adj s x
  obtain ⟨Q,hQT,hQind,hQcov⟩ := digraph_quasikernel_on_subset D T
  let U := S.filter fun s => ¬ ∃ q ∈ Q, D.Adj q s
  obtain ⟨K,hKU,hKind,hKcov⟩ := hkernel U (Finset.filter_subset _ _)
  let P := Q ∪ K
  have hfirst : ∀ s ∈ S, ∃ q ∈ P, q = s ∨ D.Adj q s := by
    intro s hs
    by_cases h : ∃ q ∈ Q, D.Adj q s
    · obtain ⟨q,hq,hqs⟩ := h
      exact ⟨q,Finset.mem_union_left _ hq,Or.inr hqs⟩
    · have hsU : s ∈ U := Finset.mem_filter.mpr ⟨hs,h⟩
      obtain ⟨k,hk,hks⟩ := hKcov s hsU
      exact ⟨k,Finset.mem_union_right _ hk,hks⟩
  refine ⟨P, ?_, ?_, hfirst, ?_⟩
  · intro a ha b hb hab
    rcases Finset.mem_union.mp ha with ha | ha <;>
      rcases Finset.mem_union.mp hb with hb | hb
    · exact hQind a ha b hb hab
    · exact fun h => (Finset.mem_filter.mp (hKU hb)).2 ⟨a,ha,h⟩
    · exact fun h => (Finset.mem_filter.mp (hQT hb)).2.2 ⟨a,(Finset.mem_filter.mp (hKU ha)).1,h⟩
    · exact hKind a ha b hb hab
  · intro v
    by_cases hvT : v ∈ T
    · obtain ⟨q,hq,h⟩ := hQcov v hvT
      refine ⟨q,Finset.mem_union_left _ hq,?_⟩
      rcases h with h | h | ⟨w,_,h1,h2⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨w,h1,h2⟩)
    · have houtside : v ∈ S ∨ ∃ s ∈ S, D.Adj s v := by
        by_contra hn
        apply hvT
        apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_univ v
        · push_neg at hn
          exact ⟨hn.1, fun ⟨s,hs,hsv⟩ => hn.2 s hs hsv⟩
      rcases houtside with hs | ⟨s,hs,hsv⟩
      · obtain ⟨q,hq,h⟩ := hfirst v hs
        exact ⟨q,hq,h.elim Or.inl (fun h => Or.inr (Or.inl h))⟩
      · obtain ⟨q,hq,h⟩ := hfirst s hs
        rcases h with h | h
        · subst q
          exact ⟨s,hq,Or.inr (Or.inl hsv)⟩
        · exact ⟨q,hq,Or.inr (Or.inr ⟨s,h,hsv⟩)⟩

  · intro v hv hvS hadj
    rcases Finset.mem_union.mp hv with hvQ | hvK
    · exact (Finset.mem_filter.mp (hQT hvQ)).2.2 hadj
    · exact hvS ((Finset.mem_filter.mp (hKU hvK)).1)
